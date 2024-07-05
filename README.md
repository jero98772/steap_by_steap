# steap_by_steap

![image](https://raw.githubusercontent.com/jero98772/steap_by_steap/main/docs/logo.jpeg)


      before i create it i was searching if "steap_by_steap" was available, and after publishing it I realized that step_by_step did too.

"steap_by_steap" is a comprehensive Python library designed to facilitate learning and implementation of fundamental algorithms and data structures. From efficient searching and sorting techniques to advanced data structures like trees and graphs, this library aims to empower developers with robust tools for algorithmic problem-solving. Whether you're a student delving into algorithms or a seasoned developer seeking reliable implementations, "steap_by_steap" provides a rich collection of algorithms, backed by clear documentation and easy integration.

steap mean:"A state when a line of code is excuting", it have the a in the middle beacause the word Algorithms start with A




### Features
List of key features:
- Binary Search
- Binary Search Tree
- B-tree
- Compression
- Convex Hull
- Directed Graph (Digraph)
- Graph
- Heap
- Interval Search Tree
- Kd-tree
- Line Segment
- Non-finite Automata
- Priority Queue
- Queue
- Regular Expressions (Regex)
- R-way Trie
- Shuffle
- Simplex Method
- Sorting Algorithms
- Stack
- Substring Search
- Suffix Array
- Ternary Search Trie
- Union-Find
- Weighted Graph

### Installation
```bash
pip install steap_by_steap
```

### Code Documentation

[https://jero98772.github.io/steap_by_steap/steap_by_steap/index.html](https://jero98772.github.io/steap_by_steap/steap_by_steap/index.html)

### Purpose
The purpose of "steap_by_steap" is to provide a comprehensive library of algorithms, enabling users to learn and implement various data structures and algorithms.

### Contribution
Contributions are welcome. If you wish to contribute, please follow the guidelines outlined in CONTRIBUTING.md.

### References
- Courses:
  - Algorithms I & II from Princeton University

### License
GPLv3 License

### Examples of use
1. **Binary Search Example:**
   ```python
   import steap_by_steap
   
   array = [1, 3, 5, 7, 9, 11, 13, 15]
   target = 7

   index = steap_by_steap.Binary_search(array, target)
   if index is not None:
       print(f"Target {target} found at index {index}")
   else:
       print(f"Target {target} not found in the array")
   ```

2. **Binary Search Tree Example:**
   ```python
   import steap_by_steap
   
   bst = steap_by_steap.BinarySearchTree()
   bst.insert(5)
   bst.insert(3)
   bst.insert(7)

   print(bst.search(3))  # Should print True
   print(bst.search(6))  # Should print False
   ```

3. **Sorting Example (Selection Sort):**
   ```python
   import steap_by_steap
   
   arr = [64, 25, 12, 22, 11]
   sorted_arr = steap_by_steap.Selection(arr)
   print(sorted_arr)  # Output should be [11, 12, 22, 25, 64]
   ```

4. **Graph Example (Depth-First Search):**
   ```python
   import steap_by_steap
   
   graph = steap_by_steap.Graph()
   graph.add_edge(0, 1)
   graph.add_edge(0, 2)
   graph.add_edge(1, 2)
   graph.add_edge(2, 0)
   graph.add_edge(2, 3)
   graph.add_edge(3, 3)

   print("Following is DFS from vertex 2:")
   graph.dfs(2)
   ```

5. **Priority Queue Example:**
   ```python
   import steap_by_steap
   
   pq = steap_by_steap.PriorityQueue()
   pq.push(4)
   pq.push(5)
   pq.push(3)
   pq.push(10)
   print(pq.pop())  # Output: 3
   print(pq.pop())  # Output: 4
   print(pq.pop())  # Output: 5
   print(pq.is_empty())  # Output: False
   ```

