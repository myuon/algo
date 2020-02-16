use bitvec::prelude::*;
use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap};
use std::hash::Hash;

#[derive(PartialEq, Eq, Debug)]
pub enum HuffmanTree<T, W> {
    Leaf(W, T),
    Node(W, Box<HuffmanTree<T, W>>, Box<HuffmanTree<T, W>>),
}

pub struct HuffmanCode<T>(HashMap<T, (u64, u8)>, HashMap<(u64, u8), T>);

impl<T: Eq + Hash + Clone> HuffmanCode<T> {
    pub fn new(code: HashMap<T, (u64, u8)>) -> Self {
        HuffmanCode(
            code.clone(),
            code.into_iter().map(|(k, v)| (v, k)).collect(),
        )
    }

    pub fn encode(&self, vec: &Vec<T>) -> Vec<u8> {
        let mut writer = BitVec::<Msb0, u8>::new();
        for t in vec.iter() {
            let b = self.0[t];
            for i in (0..b.1).rev() {
                writer.push(b.0 & (1 << i) != 0);
            }
        }

        writer.as_slice().to_vec()
    }

    pub fn decode(&self, vec: &Vec<u8>, length: usize) -> Vec<T> {
        let bitvec = BitVec::<Msb0, u8>::from_slice(&vec[..]);
        let mut decoded = Vec::new();

        let mut current = 0;
        let mut big_size = 0;
        for b in &bitvec {
            current = current * 2 + if *b { 1 } else { 0 };
            big_size += 1;
            if let Some(v) = self.1.get(&(current, big_size)) {
                decoded.push(v.clone());
                current = 0;
                big_size = 0;
            }

            if decoded.len() == length {
                break;
            }
        }

        decoded
    }

    pub fn encode_from(v: Vec<T>) -> (Self, Vec<u8>) {
        let mut h = HashMap::new();
        for t in &v {
            if !h.contains_key(t) {
                h.insert(t.clone(), 0);
            }

            h.insert(t.clone(), h.get(t).unwrap() + 1);
        }

        let code = HuffmanTree::construct(h).into_code();
        let encoded = code.encode(&v);
        (code, encoded)
    }
}

impl<T: PartialEq, W: PartialEq + PartialOrd + Copy> PartialOrd for HuffmanTree<T, W> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.weight().partial_cmp(&other.weight())
    }
}

impl<T: Eq, W: Eq + Ord + Copy> Ord for HuffmanTree<T, W> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.weight().cmp(&other.weight())
    }
}

impl<T, W: Copy> HuffmanTree<T, W> {
    pub fn weight(&self) -> W {
        use HuffmanTree::*;

        match self {
            Leaf(w, _) => *w,
            Node(w, _, _) => *w,
        }
    }
}

impl<T: Eq + Hash + Clone, W: Eq + Ord + Copy + std::ops::Add<Output = W>> HuffmanTree<T, W> {
    pub fn construct(counter: HashMap<T, W>) -> HuffmanTree<T, W> {
        if counter.is_empty() {
            panic!("Given map is empty");
        }

        let mut heap = counter
            .into_iter()
            .map(|(k, v)| Reverse(HuffmanTree::Leaf(v, k)))
            .collect::<BinaryHeap<Reverse<HuffmanTree<T, W>>>>();

        while heap.len() > 1 {
            let m1 = heap.pop().unwrap().0;
            let m2 = heap.pop().unwrap().0;
            heap.push(Reverse(HuffmanTree::Node(
                m1.weight() + m2.weight(),
                Box::new(m1),
                Box::new(m2),
            )));
        }

        heap.pop().unwrap().0
    }

    pub fn into_code(self) -> HuffmanCode<T> {
        let mut result = HashMap::new();
        self.into_code_rec(0, 0, &mut result);

        HuffmanCode::new(result)
    }

    fn into_code_rec(self, code: u64, depth: u8, acc: &mut HashMap<T, (u64, u8)>) {
        use HuffmanTree::*;

        match self {
            Leaf(_, t) => {
                acc.insert(t, (code, depth));
            }
            Node(_, t1, t2) => {
                t1.into_code_rec(code * 2, depth + 1, acc);
                t2.into_code_rec(code * 2 + 1, depth + 1, acc);
            }
        }
    }
}

#[test]
fn huffman_tree() {
    let htree = HuffmanTree::construct(
        vec![
            ("a", 5),
            ("b", 9),
            ("c", 12),
            ("d", 13),
            ("e", 16),
            ("f", 45),
        ]
        .into_iter()
        .collect(),
    );

    assert_eq!(
        htree,
        HuffmanTree::Node(
            100,
            Box::new(HuffmanTree::Leaf(45, "f")),
            Box::new(HuffmanTree::Node(
                55,
                Box::new(HuffmanTree::Node(
                    25,
                    Box::new(HuffmanTree::Leaf(12, "c")),
                    Box::new(HuffmanTree::Leaf(13, "d")),
                )),
                Box::new(HuffmanTree::Node(
                    30,
                    Box::new(HuffmanTree::Node(
                        14,
                        Box::new(HuffmanTree::Leaf(5, "a")),
                        Box::new(HuffmanTree::Leaf(9, "b"))
                    )),
                    Box::new(HuffmanTree::Leaf(16, "e"))
                )),
            )),
        )
    );

    assert_eq!(
        htree.into_code().0,
        vec![
            ("f", (0b0, 1)),
            ("c", (0b100, 3)),
            ("d", (0b101, 3)),
            ("a", (0b1100, 4)),
            ("b", (0b1101, 4)),
            ("e", (0b111, 3))
        ]
        .into_iter()
        .collect()
    );
}

#[test]
fn huffman_coding() {
    let plain = "DABCBACBBBC".chars().collect::<Vec<_>>();
    let (hcode, c) = HuffmanCode::encode_from(plain.clone());

    assert_eq!(
        hcode.0,
        vec![
            ('A', (0b111, 3)),
            ('B', (0b0, 1)),
            ('C', (0b10, 2)),
            ('D', (0b110, 3)),
        ]
        .into_iter()
        .collect::<HashMap<_, _>>()
    );
    assert_eq!(c, vec![0b11011101, 0b00111100, 0b00100000]);
    assert_eq!(hcode.decode(&c, plain.len()), plain);
}
