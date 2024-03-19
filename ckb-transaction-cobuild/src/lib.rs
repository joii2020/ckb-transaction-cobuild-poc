#![no_std]
extern crate alloc;
pub mod blake2b;
pub mod error;
pub mod lazy_reader;
pub mod log;
pub mod schemas;
pub mod schemas2;

use alloc::{collections::BTreeSet, vec::Vec};
use blake2b::{new_otx_blake2b, new_sighash_all_blake2b, new_sighash_all_only_blake2b};
use ckb_gen_types::prelude::Unpack;
use ckb_std::{
    ckb_constants::Source,
    ckb_types::packed::{CellInput, Transaction},
    error::SysError,
    high_level::{
        load_cell, load_cell_data, load_cell_lock_hash, load_cell_type_hash, load_script_hash,
        load_transaction, load_tx_hash, load_witness, QueryIter,
    },
};
use error::Error;
use schemas2::{basic, blockchain, top_level};

use core::convert::Into;
use molecule::{
    lazy_reader::Cursor,
    prelude::{Entity, Reader},
    NUMBER_SIZE,
};
use schemas::{
    basic::{Message, OtxStart},
    top_level::{WitnessLayout, WitnessLayoutReader, WitnessLayoutUnion, WitnessLayoutUnionReader},
};

///
/// This is the callback trait should be implemented in lock script by
/// developers.
pub trait Callback {
    fn invoke(&self, seal: &[u8], signing_message_hash: &[u8; 32]) -> Result<(), Error>;
}

///
/// All script_hash in `Message.Action` should be in the following set:
/// 1. all type script hashes in input cells
/// 2. all type script hashes in output cells
/// 3. all lock script hashes in input cells
///
fn check_script_hashes(hashes: BTreeSet<[u8; 32]>) -> Result<(), Error> {
    let all_hashes: BTreeSet<[u8; 32]> = QueryIter::new(load_cell_type_hash, Source::Input)
        .chain(QueryIter::new(load_cell_type_hash, Source::Output))
        .filter_map(|f| f)
        .chain(QueryIter::new(load_cell_lock_hash, Source::Input))
        .collect();
    if hashes.is_subset(&all_hashes) {
        Ok(())
    } else {
        Err(Error::ScriptHashAbsent)
    }
}

///
/// fetch the seal field of SighashAll or SighashAllOnly in current script group
///
fn fetch_seal() -> Result<Vec<u8>, Error> {
    match load_witness(0, Source::GroupInput) {
        Ok(witness) => {
            if let Ok(r) = WitnessLayoutReader::from_slice(&witness) {
                match r.to_enum() {
                    WitnessLayoutUnionReader::SighashAll(s) => Ok(s.seal().raw_data().to_vec()),
                    WitnessLayoutUnionReader::SighashAllOnly(s) => Ok(s.seal().raw_data().to_vec()),
                    _ => Err(Error::MoleculeEncoding),
                }
            } else {
                Err(Error::MoleculeEncoding)
            }
        }
        Err(e) => Err(e.into()),
    }
}

///
/// fetch the message field of SighashAll
/// returns None if there is no SighashAll witness
/// returns Error::WrongWitnessLayout if there are more than one SighashAll witness
pub fn fetch_message() -> Result<Option<Message>, Error> {
    let mut iter = QueryIter::new(load_witness, Source::Input).filter_map(|witness| {
        WitnessLayoutReader::from_slice(&witness)
            .ok()
            .and_then(|r| match r.to_enum() {
                WitnessLayoutUnionReader::SighashAll(s) => Some(s.message().to_entity()),
                _ => None,
            })
    });

    match (iter.next(), iter.next()) {
        (Some(message), None) => Ok(Some(message)),
        (None, None) => Ok(None),
        _ => Err(Error::WrongWitnessLayout),
    }
}

///
/// for lock script with message, the other witness in script group except
/// first one should be empty
///
fn check_others_in_group() -> Result<(), Error> {
    if QueryIter::new(load_witness, Source::GroupInput)
        .skip(1)
        .all(|witness| witness.is_empty())
    {
        Ok(())
    } else {
        Err(Error::WrongWitnessLayout)
    }
}

fn generate_signing_message_hash(message: &Option<Message>) -> Result<[u8; 32], Error> {
    // message
    let mut hasher = match message {
        Some(m) => {
            let mut hasher = new_sighash_all_blake2b();
            hasher.update(m.as_slice());
            hasher
        }
        None => new_sighash_all_only_blake2b(),
    };
    // tx hash
    hasher.update(&load_tx_hash()?);
    // inputs cell and data
    let inputs_len = calculate_inputs_len()?;
    for i in 0..inputs_len {
        let input_cell = load_cell(i, Source::Input)?;
        hasher.update(input_cell.as_slice());
        // TODO cell data may be too large, use high_level::load_data fn to load and hash it in chunks
        let input_cell_data = load_cell_data(i, Source::Input)?;
        hasher.update(&(input_cell_data.len() as u32).to_le_bytes());
        hasher.update(&input_cell_data);
    }
    // extra witnesses
    for witness in QueryIter::new(load_witness, Source::Input).skip(inputs_len) {
        hasher.update(&(witness.len() as u32).to_le_bytes());
        hasher.update(&witness);
    }

    let mut result = [0u8; 32];
    let count = hasher.count();
    hasher.finalize(&mut result);
    log!(
        "generate_signing_message_hash totally hashed {} bytes, hash = {:?}",
        count,
        result
    );
    Ok(result)
}

///
/// the molecule data structure of transaction is:
/// full-size|raw-offset|witnesses-offset|raw-full-size|version-offset|cell_deps-offset|header_deps-offset|inputs-offset|outputs-offset|...
/// full-size and offset are 4 bytes, so we can read the inputs-offset and outputs-offset at [28, 36),
/// then we can get the length of inputs by calculating the difference between inputs-offset and outputs-offset
///
fn calculate_inputs_len() -> Result<usize, SysError> {
    let mut offsets = [0u8; 8];
    match ckb_std::syscalls::load_transaction(&mut offsets, 28) {
        // this syscall will always return SysError::LengthNotEnough since we only load 8 bytes, let's ignore it
        Err(SysError::LengthNotEnough(_)) => {}
        Err(SysError::Unknown(e)) => return Err(SysError::Unknown(e)),
        _ => unreachable!(),
    }
    let inputs_offset = u32::from_le_bytes(offsets[0..4].try_into().unwrap());
    let outputs_offset = u32::from_le_bytes(offsets[4..8].try_into().unwrap());
    Ok((outputs_offset as usize - inputs_offset as usize - NUMBER_SIZE) / CellInput::TOTAL_SIZE)
}

pub fn cobuild_normal_entry<F: Callback>(verifier: F) -> Result<(), Error> {
    check_others_in_group()?;
    let message = fetch_message()?;
    let signing_message_hash = generate_signing_message_hash(&message)?;
    let seal = fetch_seal()?;
    verifier.invoke(&seal, &signing_message_hash)?;
    Ok(())
}

///
/// Parse all witness into WitnessLayout structure if possible. It is none if
/// isn't. For example, if it is a WitnessArgs structure, it is none. The second
/// value indicates the cobuild is activated or not.
///
pub fn parse_witness_layouts(tx: &Transaction) -> (Vec<Option<WitnessLayout>>, bool) {
    let witness_layouts: Vec<Option<WitnessLayout>> = tx
        .witnesses()
        .into_iter()
        .map(|w| WitnessLayout::from_slice(&w.raw_data()).ok())
        .collect();
    let activated = witness_layouts.iter().any(|w| w.is_some());
    (witness_layouts, activated)
}

pub fn parse_witness_layouts2(
    tx: &blockchain::Transaction,
) -> (Vec<Option<top_level::WitnessLayout>>, bool) {
    let witness_layouts: Vec<Option<top_level::WitnessLayout>> = tx
        .witnesses()
        .unwrap()
        .into_iter()
        .map(|w| top_level::WitnessLayout::try_from(w).ok())
        .collect();
    for w in &witness_layouts {
        if let Some(w2) = w {
            w2.verify(false).unwrap();
        }
    }
    let activated = witness_layouts.iter().any(|w| w.is_some());
    (witness_layouts, activated)
}

///
/// verify all otx messages with the given script hash and verify function
/// This function is mainly used by lock script
///
pub fn cobuild_entry<F: Callback>(verifier: F) -> Result<bool, Error> {
    let tx_reader = lazy_reader::TransactionReader::new();
    let cursor: Cursor = tx_reader.into();
    let lazy_tx = blockchain::Transaction::from(cursor);

    let tx = load_transaction()?;
    let raw_tx = tx.raw();

    let (witness_layouts, cobuild_activated) = parse_witness_layouts(&tx);
    let (witness_layouts2, cobuild_activated2) = parse_witness_layouts2(&lazy_tx);
    assert_eq!(cobuild_activated, cobuild_activated2);
    // Legacy Flow Handling
    if !cobuild_activated {
        return Ok(false);
    }

    let current_script_hash = load_script_hash()?;
    // step 2
    // step 4
    let (otx_start, i) = fetch_otx_start()?;
    let (otx_start2, i2) = fetch_otx_start2(&witness_layouts2)?;
    assert_eq!(i, i2);
    assert_eq!(otx_start.is_none(), otx_start2.is_none());
    if otx_start.is_none() {
        // step 3
        log!("No otx detected");
        cobuild_normal_entry(verifier)?;
        return Ok(true);
    }
    let otx_start = otx_start.unwrap();
    let otx_start2 = otx_start2.unwrap();

    let start_input_cell: u32 = otx_start.start_input_cell().unpack();
    let start_output_cell: u32 = otx_start.start_output_cell().unpack();
    let start_cell_deps: u32 = otx_start.start_cell_deps().unpack();
    let start_header_deps: u32 = otx_start.start_header_deps().unpack();

    let start_input_cell2: u32 = otx_start2.start_input_cell().unwrap();
    let start_output_cell2: u32 = otx_start2.start_output_cell().unwrap();
    let start_cell_deps2: u32 = otx_start2.start_cell_deps().unwrap();
    let start_header_deps2: u32 = otx_start2.start_header_deps().unwrap();
    assert_eq!(start_input_cell, start_input_cell2);
    assert_eq!(start_output_cell, start_output_cell2);
    assert_eq!(start_cell_deps, start_cell_deps2);
    assert_eq!(start_header_deps, start_header_deps2);
    // abbrev. from spec:
    // ie = input end
    // is = input start
    // oe = output end
    // os = output start
    // ce = cell deps end
    // cs = cell deps start
    // he = header dep end
    // hs = header dep start
    // step 5
    let mut ie = start_input_cell as usize;
    let is = ie;
    let mut oe = start_output_cell as usize;
    let mut ce = start_cell_deps as usize;
    let mut he = start_header_deps as usize;
    let mut execution_count: usize = 0;
    let mut otx_count = 0;
    log!("ie = {}, oe = {}, ce = {}, he = {}", ie, oe, ce, he);
    log!("Otx starts at index {}(inclusive)", i + 1);
    // this index is always pointing to the current processing OTX witness.
    let mut index = i;
    for witness in witness_layouts.iter().skip(i + 1) {
        index += 1;
        if witness.is_none() {
            // step 6, not WitnessLayoutOtx
            break;
        }
        match witness.as_ref().unwrap().to_enum() {
            WitnessLayoutUnion::Otx(otx) => {
                otx_count += 1;
                let input_cells: u32 = otx.input_cells().unpack();
                let output_cells: u32 = otx.output_cells().unpack();
                let cell_deps: u32 = otx.cell_deps().unpack();
                let header_deps: u32 = otx.header_deps().unpack();
                // step 6.b
                if input_cells == 0 && output_cells == 0 && cell_deps == 0 && header_deps == 0 {
                    return Err(Error::WrongCount);
                }
                let action_hashes: BTreeSet<[u8; 32]> = otx
                    .as_reader()
                    .message()
                    .actions()
                    .iter()
                    .map(|pair| pair.script_hash().raw_data().try_into().unwrap())
                    .collect();
                // step 6.c
                check_script_hashes(action_hashes)?;
                // step 6.d
                let lock_hash_existing = QueryIter::new(load_cell_lock_hash, Source::Input)
                    .skip(ie)
                    .take(input_cells as usize)
                    .any(|hash| hash == current_script_hash);
                if !lock_hash_existing {
                    ie += input_cells as usize;
                    oe += output_cells as usize;
                    ce += cell_deps as usize;
                    he += header_deps as usize;
                    continue;
                }
                // step 6.e
                let smh = generate_otx_smh(&otx, &raw_tx, ie, oe, ce, he)?;
                // step 6.f
                let mut seal_found = false;
                for seal_pair in otx.as_reader().seals().iter() {
                    if seal_pair.script_hash().as_slice() == current_script_hash.as_slice() {
                        verifier.invoke(&seal_pair.seal().raw_data(), &smh)?;
                        seal_found = true;
                        execution_count += 1;
                        break;
                        // duplicated seals are ignored
                    }
                }
                if !seal_found {
                    log!("seal can't be found");
                    return Err(Error::NoSealFound);
                }
                // step 6.h
                ie += input_cells as usize;
                oe += output_cells as usize;
                ce += cell_deps as usize;
                he += header_deps as usize;
            }
            // step 6
            WitnessLayoutUnion::SighashAll(_) => break,
            WitnessLayoutUnion::SighashAllOnly(_) => break,
            WitnessLayoutUnion::OtxStart(_) => return Err(Error::WrongWitnessLayout),
        }
    } // end of step 6 loop
      // step 7
      // after the loop, the `index` points to the first non OTX witness
    let j = index + 1;
    log!("the first non OTX witness is at index {}", j);
    for index in 0..witness_layouts.len() {
        // [0, i) [j, +infinity)
        if index < i || index >= j {
            if let Some(r) = &witness_layouts[index] {
                match r.to_enum() {
                    WitnessLayoutUnion::Otx(_) => {
                        log!(
                            "WrongWitnessLayout at index = {} (i = {}, j = {}, otx_count = {})",
                            index,
                            i,
                            j,
                            otx_count
                        );
                        return Err(Error::WrongWitnessLayout);
                    }
                    _ => {}
                }
            }
        }
    }
    // step 8
    let mut found = false;
    for index in 0..raw_tx.inputs().len() {
        // scan all input cell in [0, is) and [ie, +infinity)
        // if is == ie, it is always true
        if index < is || index >= ie {
            let hash = load_cell_lock_hash(index, Source::Input)?;
            if hash == current_script_hash {
                found = true;
                break;
            }
        }
    }
    if found {
        execution_count += 1;
        log!("extra callback is invoked");
        cobuild_normal_entry(verifier)?;
    }
    log!("execution_count = {}", execution_count);
    Ok(true)
}

/// generate OTX signing message hash
fn generate_otx_smh(
    otx: &schemas::basic::Otx,
    raw_tx: &ckb_std::ckb_types::packed::RawTransaction,
    ie: usize,
    oe: usize,
    ce: usize,
    he: usize,
) -> Result<[u8; 32], Error> {
    log!("ie = {}, oe = {}, ce = {}, he = {}", ie, oe, ce, he);
    let input_cells: u32 = otx.input_cells().unpack();
    let output_cells: u32 = otx.output_cells().unpack();
    let cell_deps: u32 = otx.cell_deps().unpack();
    let header_deps: u32 = otx.header_deps().unpack();

    let mut hasher = new_otx_blake2b();
    hasher.update(otx.message().as_slice());
    hasher.update(&input_cells.to_le_bytes());
    let input_iter = raw_tx
        .inputs()
        .into_iter()
        .skip(ie)
        .zip(QueryIter::new(load_cell, Source::Input).skip(ie))
        .zip(QueryIter::new(load_cell_data, Source::Input).skip(ie));
    let mut count = 0;
    for ((input, input_cell), input_cell_data) in input_iter.take(input_cells as usize) {
        hasher.update(input.as_slice());
        hasher.update(input_cell.as_slice());
        hasher.update(&(input_cell_data.len() as u32).to_le_bytes());
        hasher.update(&input_cell_data);
        count += 1;
    }
    // It's important to verify count. Consider the scenario that the all
    // count(input_cells, output_cells, cell_deps, header_deps) are zero due to
    // `iterator::take` method. The hash result can be a predictable.
    if count != input_cells {
        return Err(Error::WrongCount);
    }
    hasher.update(&output_cells.to_le_bytes());
    let output_iter = raw_tx
        .outputs()
        .into_iter()
        .skip(oe)
        .zip(raw_tx.outputs_data().into_iter().skip(oe));
    let mut count = 0;
    for (output_cell, output_cell_data) in output_iter.take(output_cells as usize) {
        hasher.update(output_cell.as_slice());
        hasher.update(output_cell_data.as_slice());
        count += 1;
    }
    if count != output_cells {
        return Err(Error::WrongCount);
    }
    hasher.update(&cell_deps.to_le_bytes());
    let cell_dep_iter = raw_tx.cell_deps().into_iter().skip(ce);
    let mut count = 0;
    for cell_dep in cell_dep_iter.take(cell_deps as usize) {
        hasher.update(cell_dep.as_slice());
        count += 1;
    }
    if count != cell_deps {
        return Err(Error::WrongCount);
    }
    hasher.update(&header_deps.to_le_bytes());
    let header_dep_iter = raw_tx.header_deps().into_iter().skip(he);
    let mut count = 0;
    for header_dep in header_dep_iter.take(header_deps as usize) {
        hasher.update(header_dep.as_slice());
        count += 1;
    }
    if count != header_deps {
        return Err(Error::WrongCount);
    }
    let mut result = [0u8; 32];
    let count = hasher.count();
    hasher.finalize(&mut result);
    log!(
        "generate_otx_smh totally hashed {} bytes and hash is {:?}",
        count,
        result
    );
    Ok(result)
}

// TODO
/// generate OTX signing message hash
// fn generate_otx_smh2(
//     otx: &schemas2::basic::Otx,
//     raw_tx: &blockchain::RawTransaction,
//     ie: usize,
//     oe: usize,
//     ce: usize,
//     he: usize,
// ) -> Result<[u8; 32], Error> {
//     log!("ie = {}, oe = {}, ce = {}, he = {}", ie, oe, ce, he);
//     let input_cells: u32 = otx.input_cells()?;
//     let output_cells: u32 = otx.output_cells()?;
//     let cell_deps: u32 = otx.cell_deps()?;
//     let header_deps: u32 = otx.header_deps()?;

//     let mut hasher = new_otx_blake2b();
//     hasher.update_cursor(otx.message()?.cursor.clone());
//     hasher.update(&input_cells.to_le_bytes());
//     let input_iter = raw_tx
//         .inputs()
//         .into_iter()
//         .skip(ie)
//         .zip(QueryIter::new(load_cell, Source::Input).skip(ie))
//         .zip(QueryIter::new(load_cell_data, Source::Input).skip(ie));
//     let mut count = 0;
//     for ((input, input_cell), input_cell_data) in input_iter.take(input_cells as usize) {
//         hasher.update(input.as_slice());
//         hasher.update(input_cell.as_slice());
//         hasher.update(&(input_cell_data.len() as u32).to_le_bytes());
//         hasher.update(&input_cell_data);
//         count += 1;
//     }
//     // It's important to verify count. Consider the scenario that the all
//     // count(input_cells, output_cells, cell_deps, header_deps) are zero due to
//     // `iterator::take` method. The hash result can be a predictable.
//     if count != input_cells {
//         return Err(Error::WrongCount);
//     }
//     hasher.update(&output_cells.to_le_bytes());
//     let output_iter = raw_tx
//         .outputs()
//         .into_iter()
//         .skip(oe)
//         .zip(raw_tx.outputs_data().into_iter().skip(oe));
//     let mut count = 0;
//     for (output_cell, output_cell_data) in output_iter.take(output_cells as usize) {
//         hasher.update(output_cell.as_slice());
//         hasher.update(output_cell_data.as_slice());
//         count += 1;
//     }
//     if count != output_cells {
//         return Err(Error::WrongCount);
//     }
//     hasher.update(&cell_deps.to_le_bytes());
//     let cell_dep_iter = raw_tx.cell_deps().into_iter().skip(ce);
//     let mut count = 0;
//     for cell_dep in cell_dep_iter.take(cell_deps as usize) {
//         hasher.update(cell_dep.as_slice());
//         count += 1;
//     }
//     if count != cell_deps {
//         return Err(Error::WrongCount);
//     }
//     hasher.update(&header_deps.to_le_bytes());
//     let header_dep_iter = raw_tx.header_deps().into_iter().skip(he);
//     let mut count = 0;
//     for header_dep in header_dep_iter.take(header_deps as usize) {
//         hasher.update(header_dep.as_slice());
//         count += 1;
//     }
//     if count != header_deps {
//         return Err(Error::WrongCount);
//     }
//     let mut result = [0u8; 32];
//     let count = hasher.count();
//     hasher.finalize(&mut result);
//     log!(
//         "generate_otx_smh totally hashed {} bytes and hash is {:?}",
//         count,
//         result
//     );
//     Ok(result)
// }

fn fetch_otx_start() -> Result<(Option<OtxStart>, usize), Error> {
    let mut otx_start = None;
    let mut start_index = 0;
    let mut end_index = 0;

    for (i, witness) in QueryIter::new(load_witness, Source::Input).enumerate() {
        if let Ok(r) = WitnessLayoutReader::from_slice(&witness) {
            match r.to_enum() {
                WitnessLayoutUnionReader::OtxStart(o) => {
                    if otx_start.is_none() {
                        otx_start = Some(o.to_entity());
                        start_index = i;
                        end_index = i;
                    } else {
                        log!("Duplicated OtxStart found");
                        return Err(Error::WrongWitnessLayout);
                    }
                }
                WitnessLayoutUnionReader::Otx(_) => {
                    if otx_start.is_none() {
                        log!("A Otx without OtxStart found");
                        return Err(Error::WrongWitnessLayout);
                    } else {
                        if end_index + 1 != i {
                            log!("Otx are not continuous");
                            return Err(Error::WrongWitnessLayout);
                        } else {
                            end_index = i;
                        }
                    }
                }
                _ => {}
            }
        }
    }
    if otx_start.is_some() {
        if end_index > 0 {
            return Ok((otx_start, start_index));
        } else {
            log!("end_index == 0, there is no OTX");
            return Err(Error::WrongOtxStart);
        }
    } else {
        Ok((None, 0))
    }
}

fn fetch_otx_start2(
    witnesses: &Vec<Option<top_level::WitnessLayout>>,
) -> Result<(Option<basic::OtxStart>, usize), Error> {
    let mut otx_start = None;
    let mut start_index = 0;
    let mut end_index = 0;

    for (i, witness) in witnesses.iter().enumerate() {
        if let Some(witness_layout) = witness {
            match witness_layout {
                top_level::WitnessLayout::OtxStart(start) => {
                    if otx_start.is_none() {
                        otx_start = Some(start.cursor.clone().into());
                        start_index = i;
                        end_index = i;
                    } else {
                        log!("Duplicated OtxStart found");
                        return Err(Error::WrongWitnessLayout);
                    }
                }
                top_level::WitnessLayout::Otx(_) => {
                    if otx_start.is_none() {
                        log!("A Otx without OtxStart found");
                        return Err(Error::WrongWitnessLayout);
                    } else {
                        if end_index + 1 != i {
                            log!("Otx are not continuous");
                            return Err(Error::WrongWitnessLayout);
                        } else {
                            end_index = i;
                        }
                    }
                }
                _ => {}
            }
        }
    }

    if otx_start.is_some() {
        if end_index > 0 {
            return Ok((otx_start, start_index));
        } else {
            log!("end_index == 0, there is no OTX");
            return Err(Error::WrongOtxStart);
        }
    } else {
        Ok((None, 0))
    }
}
