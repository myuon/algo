use bitvec::prelude::*;
use std::io::Read;

pub struct Window {
    block_size: u64,
    buffer: Vec<u8>,
}

impl Window {
    pub fn new(block_size: u64) -> Self {
        Window {
            block_size,
            buffer: Vec::new(),
        }
    }

    pub fn search(&self, input: &[u8]) -> SearchResult {
        for i in 0..(self.block_size as usize).min(self.buffer.len()) {
            for k in (1..=input.len().min(self.buffer.len())).rev() {
                if self.buffer.len() < i + k {
                    continue;
                }

                if self.buffer[self.buffer.len() - i - k..self.buffer.len() - i] == input[0..k] {
                    return SearchResult::Found(i + k, k);
                }
            }
        }

        SearchResult::NotFound(input[0])
    }

    pub fn append(&mut self, mut input: Vec<u8>) {
        if self.block_size >= self.block_size * 2 {
            let new_buf = self.buffer
                [self.buffer.len() - 1 - self.block_size as usize..self.buffer.len() - 1]
                .to_vec();
            self.buffer = new_buf;
        }

        self.buffer.append(&mut input);
    }
}

#[test]
fn test_window() {
    let window = Window {
        block_size: 10,
        buffer: vec![1, 2, 3, 9, 5, 6, 7, 8, 9, 10],
    };

    assert_eq!(window.search(&[1, 2, 3]), SearchResult::Found(10, 3));
    assert_eq!(window.search(&[5, 6, 10]), SearchResult::Found(6, 2));
    assert_eq!(window.search(&[10]), SearchResult::Found(1, 1));
    assert_eq!(window.search(&[9]), SearchResult::Found(2, 1));
}

#[derive(Clone, Debug, PartialEq)]
pub enum SearchResult {
    Found(usize, usize),
    NotFound(u8),
}

impl SearchResult {
    fn len(&self) -> usize {
        use SearchResult::*;

        match self {
            Found(_, u) => *u,
            NotFound(_) => 1,
        }
    }

    fn to_vec(&self) -> Vec<u8> {
        use SearchResult::*;

        let mut bv = BitVec::<Msb0, u8>::new();
        match self {
            Found(a, b) => {
                bv.push(true);
                bv.push(a & 8 != 0);
                bv.push(a & 4 != 0);
                bv.push(a & 2 != 0);
                bv.push(a & 1 != 0);
                bv.push(b & 4 != 0);
                bv.push(b & 2 != 0);
                bv.push(b & 1 != 0);
            }
            NotFound(c) => {
                bv.push(false);
                bv.push(c & 64 != 0);
                bv.push(c & 32 != 0);
                bv.push(c & 16 != 0);
                bv.push(c & 8 != 0);
                bv.push(c & 4 != 0);
                bv.push(c & 2 != 0);
                bv.push(c & 1 != 0);
            }
        }

        bv.as_slice().to_vec()
    }
}

pub struct Lzss {
    block_size: u64,
    search_size: u64,
}

impl Lzss {
    pub fn new(block_size: u64, search_size: u64) -> Self {
        Lzss {
            block_size,
            search_size,
        }
    }

    pub fn default() -> Self {
        Lzss {
            block_size: 8192,
            search_size: 3,
        }
    }

    pub fn encode(&self, input: &mut impl Read) -> Vec<u8> {
        self.search_results(input)
            .into_iter()
            .flat_map(|r| r.to_vec())
            .collect()
    }

    pub fn search_results(&self, input: &mut impl Read) -> Vec<SearchResult> {
        let mut encoded = Vec::new();
        let mut window = Window::new(self.block_size);

        // 簡単のため読み込みはブロックごととしているが、これではブロックの境界を超えてmatchするものが読めない
        // 本来はbufも先読みをし続けなければならない
        let mut buf = vec![0; self.block_size as usize];
        while let Ok(bytes) = input.read(&mut buf) {
            if bytes == 0 {
                break;
            }

            // どこまで読んだか
            let mut p = 0;

            while p < bytes {
                let result = window.search(&buf[p..p + self.search_size as usize]);
                encoded.push(result.clone());
                window.append(buf[p..p + result.len()].to_vec());

                p += result.len();
            }
        }

        encoded
    }
}

#[test]
fn lzss_search_results() {
    use std::io::Cursor;

    let lzss = Lzss::default();
    let mut input = Cursor::new("ABBABCAAB");
    assert_eq!(
        lzss.search_results(&mut input),
        vec![
            SearchResult::NotFound(65),
            SearchResult::NotFound(66),
            SearchResult::Found(1, 1),
            SearchResult::Found(3, 2),
            SearchResult::NotFound(67),
            SearchResult::Found(3, 1),
            SearchResult::Found(1, 1),
            SearchResult::Found(4, 1)
        ]
    );
}
