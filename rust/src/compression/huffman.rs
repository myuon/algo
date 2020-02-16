use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap};
use std::hash::Hash;

#[derive(PartialEq, Eq, Debug)]
pub enum HuffmanTree<T, W> {
    Leaf(W, T),
    Node(W, Box<HuffmanTree<T, W>>, Box<HuffmanTree<T, W>>),
}

pub struct HuffmanCode<T>(HashMap<T, u32>, HashMap<u32, T>);

impl<T: Eq + Hash + Clone> HuffmanCode<T> {
    pub fn new(code: HashMap<T, u32>) -> Self {
        HuffmanCode(
            code.clone(),
            code.into_iter().map(|(k, v)| (v, k)).collect(),
        )
    }

    pub fn encode(&self, vec: &Vec<T>) -> Vec<u32> {
        vec.iter()
            .map(move |t| self.0.get(t).unwrap())
            .cloned()
            .collect()
    }

    pub fn decode(&self, vec: &Vec<u32>) -> Vec<T> {
        vec.iter()
            .map(move |t| self.1.get(t).unwrap())
            .cloned()
            .collect()
    }

    pub fn encode_from(v: Vec<T>) -> (Self, Vec<u32>) {
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
        self.into_code_rec(0, &mut result);

        HuffmanCode::new(result)
    }

    fn into_code_rec(self, code: u32, acc: &mut HashMap<T, u32>) {
        use HuffmanTree::*;

        match self {
            Leaf(_, t) => {
                acc.insert(t, code);
            }
            Node(_, t1, t2) => {
                t1.into_code_rec(code * 2, acc);
                t2.into_code_rec(code * 2 + 1, acc);
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
            ("f", 0b0),
            ("c", 0b100),
            ("d", 0b101),
            ("a", 0b1100),
            ("b", 0b1101),
            ("e", 0b111)
        ]
        .into_iter()
        .collect()
    );
}

#[test]
fn huffman_coding() {
    let plain = "DAEBCBACBBBC".chars().collect::<Vec<_>>();
    let (hcode, c) = HuffmanCode::encode_from(plain.clone());

    assert_eq!(hcode.decode(&c), plain);
    assert_eq!(
        c,
        vec![0b1110, 0b110, 0b1111, 0b0, 0b10, 0b0, 0b110, 0b10, 0b0, 0b0, 0b0, 0b10]
    );
}
