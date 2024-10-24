// src/lib.rs
use pyo3::prelude::*;
use pyo3::wrap_pyfunction;

mod stack;
mod queue;
mod binarysearchtree;
mod binarysearch;
mod unionfind;
mod sort;
mod shuffle;
mod convexhull;
mod heap;
mod priorityqueue;
mod btree;
mod linesegment;
mod kdtree;
mod intervalsearchtree;
mod graph;
mod digraph;
mod weightedgraph;
mod suffixarray;
mod rwaytrie;
mod ternarysearchtrie;
mod substringsearch;
mod nonfiniteautomata;
mod regex;
mod compression;
mod simplexmethod;
mod criptografy;


use unionfind::UnionFind;
use binarysearch::Binary_search;
use binarysearchtree::BinarySearchTree;
use btree::BTree;
use kdtree::KdTree;
use shuffle::Knuth;
use graph::Graph;
use digraph::Digraph;
use regex::Regex;
use simplexmethod::Simplex;
use weightedgraph::WeightedGraph;
use suffixarray::SuffixArray;
use rwaytrie::RWayTrie;
use ternarysearchtrie::TernarySearchTrie;
use convexhull::Convex_hull;
use intervalsearchtree::{IntervalTree};
use priorityqueue::PriorityQueue;
use heap::{Heap,Heapsort};
use stack::{StackI32,StackF64};
use queue::{QueueI32,QueueF64};
use linesegment::{LineSegment};
use nonfiniteautomata::{NFA,Symbol,State};
use substringsearch::{BrutalForceSearch,KMPSearch,BoyerMooreSearch,RabinKarpSearch};
use sort::{Selection,Insertion,Shell,Quick,Merge,MsdRadix,LsdRadix,RadixQuicksort};
use compression::{HuffmanCodes,RunLengthEncode,RunLengthDecode,LZWCompress,LZWDecompress,HuffmanDecompress,HuffmanCompress,DecompressImageFFT,CompressImageFFT};
use criptografy::{DecryptXOR,EncryptXOR,EncryptRSA,GenerateKey,DecryptRSA,RandomPrime,DecryptCesar,EncryptCesar,EncryptRailFence,DecryptRailFence};

#[pymodule]
fn steap_by_steap(m: &PyModule) -> PyResult<()> {

    m.add_class::<UnionFind>()?;
    m.add_class::<StackI32>()?;
    m.add_class::<StackF64>()?;
    m.add_class::<QueueI32>()?;
    m.add_class::<QueueF64>()?;
    m.add_class::<Heap>()?;
    m.add_class::<BinarySearchTree>()?;
    m.add_class::<PriorityQueue>()?;
    m.add_class::<BTree>()?;
    m.add_class::<LineSegment>()?;
    m.add_class::<KdTree>()?;
    m.add_class::<IntervalTree>()?;
    m.add_class::<Graph>()?;
    m.add_class::<Digraph>()?;
    m.add_class::<WeightedGraph>()?;
    m.add_class::<SuffixArray>()?;
    m.add_class::<RWayTrie>()?;
    m.add_class::<TernarySearchTrie>()?;
    m.add_class::<NFA>()?;;
    m.add_class::<Symbol>()?;
    m.add_class::<State>()?;
    m.add_class::<Regex>()?;
    m.add_class::<Simplex>()?;

    m.add_function(wrap_pyfunction!(Binary_search, m)?)?;
    m.add_function(wrap_pyfunction!(Selection, m)?)?;
    m.add_function(wrap_pyfunction!(Insertion, m)?)?;
    m.add_function(wrap_pyfunction!(Shell, m)?)?;
    m.add_function(wrap_pyfunction!(Quick, m)?)?;
    m.add_function(wrap_pyfunction!(Merge, m)?)?;
    m.add_function(wrap_pyfunction!(Knuth, m)?)?;
    m.add_function(wrap_pyfunction!(Convex_hull, m)?)?;
    m.add_function(wrap_pyfunction!(Heapsort, m)?)?;
    m.add_function(wrap_pyfunction!(MsdRadix, m)?)?;
    m.add_function(wrap_pyfunction!(LsdRadix, m)?)?;
    m.add_function(wrap_pyfunction!(RadixQuicksort, m)?)?;
    m.add_function(wrap_pyfunction!(BrutalForceSearch, m)?)?;
    m.add_function(wrap_pyfunction!(KMPSearch, m)?)?;
    m.add_function(wrap_pyfunction!(BoyerMooreSearch, m)?)?;
    m.add_function(wrap_pyfunction!(RabinKarpSearch, m)?)?;
    m.add_function(wrap_pyfunction!(HuffmanCodes, m)?)?;
    m.add_function(wrap_pyfunction!(RunLengthEncode, m)?)?;
    m.add_function(wrap_pyfunction!(RunLengthDecode, m)?)?;
    m.add_function(wrap_pyfunction!(LZWCompress, m)?)?;
    m.add_function(wrap_pyfunction!(LZWDecompress, m)?)?;
    m.add_function(wrap_pyfunction!(HuffmanCompress, m)?)?;
    m.add_function(wrap_pyfunction!(HuffmanDecompress, m)?)?;
    m.add_function(wrap_pyfunction!(EncryptXOR, m)?)?;
    m.add_function(wrap_pyfunction!(DecryptXOR, m)?)?;
    m.add_function(wrap_pyfunction!(CompressImageFFT, m)?)?;
    m.add_function(wrap_pyfunction!(DecompressImageFFT, m)?)?;
    m.add_function(wrap_pyfunction!(EncryptCesar, m)?)?;
    m.add_function(wrap_pyfunction!(EncryptRailFence, m)?)?;
    m.add_function(wrap_pyfunction!(DecryptCesar, m)?)?;
    m.add_function(wrap_pyfunction!(DecryptRailFence, m)?)?;
    m.add_function(wrap_pyfunction!(RandomPrime, m)?)?;
    m.add_function(wrap_pyfunction!(GenerateKey, m)?)?;
    m.add_function(wrap_pyfunction!(EncryptRSA, m)?)?;
    m.add_function(wrap_pyfunction!(DecryptRSA, m)?)?;
    Ok(())
}
  