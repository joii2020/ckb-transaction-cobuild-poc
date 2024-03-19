use core::cmp::min;

use alloc::boxed::Box;
use ckb_std::{error::SysError, syscalls};
use molecule::lazy_reader::{Cursor, Error, Read};

use crate::log;

pub struct TransactionReader {
    pub total_length: usize,
}

impl TransactionReader {
    pub fn new() -> Self {
        let mut buf = [0u8; 4];
        let result = syscalls::load_transaction(&mut buf, 0);
        let total_length = match result {
            Ok(l) => l,
            Err(e) => match e {
                SysError::LengthNotEnough(l) => l,
                _ => panic!("error on load_transaction"),
            },
        };
        Self { total_length }
    }
}

impl Read for TransactionReader {
    fn read(&self, buf: &mut [u8], offset: usize) -> Result<usize, Error> {
        log!(
            "try to read {} bytes into buffer with offset {}",
            buf.len(),
            offset
        );
        if offset >= self.total_length {
            return Err(Error::OutOfBound(offset, self.total_length));
        }

        let remaining_len = self.total_length - offset;
        let min_len = min(remaining_len, buf.len());

        if (offset + min_len) > self.total_length {
            return Err(Error::OutOfBound(offset + min_len, self.total_length));
        }
        let actual_len = syscalls::load_transaction(buf, offset).map_err(|_| Error::Common)?;
        let read_len = min(buf.len(), actual_len);
        log!("totally read {} bytes", read_len);
        Ok(read_len)
    }
}

impl From<TransactionReader> for Cursor {
    fn from(data: TransactionReader) -> Self {
        Cursor::new(data.total_length, Box::new(data))
    }
}
