import steap_by_steap

sa = steap_by_steap.SuffixArray('banana')
print(sa.get_suffix_array(),"must be [5, 3, 1, 0, 4, 2]")
print(sa.search("ana"),"\n\n")#3



c=steap_by_steap.LZWCompress("helloo")
print(c)
d=steap_by_steap.LZWDecompress(c)
print(str(d),"\n\n")

image=0
if image:

    d,hc=steap_by_steap.HuffmanCompress("hellooo")
    hd=steap_by_steap.HuffmanDecompress(d,hc)
    print(hc,hd)

    inimg="1.jpg"
    outimg="ans.jpg"
    r=0.99
    steap_by_steap.CompressImageFFT(inimg,outimg,r)
    steap_by_steap.DecompressImageFFT(outimg,"ans2.jpg")


#print(dir(steap_by_steap))
uf = steap_by_steap.UnionFind(10)

uf.union(0, 1)
uf.union(2, 3)
uf.union(4, 5)
uf.union(6, 7)

print(f"Is 1 and 2 in the same set? {uf.same_set(1, 2)}")  # Should print "false"
print(f"Is 3 and 4 in the same set? {uf.same_set(3, 4)}")  # Should print "false"

uf.union(1, 2)
uf.union(3, 4)

print(f"Is 1 and 2 in the same set? {uf.same_set(1, 2)}")  # Should print "true"
print(f"Is 3 and 4 in the same set? {uf.same_set(3, 4)}")  # Should print "true"

s32 = steap_by_steap.StackI32()

s32.push(1)
s32.push(2)
s32.push(3)
s32.push(5)
s32.pop()
s32.pop()
s32.print()

q32 = steap_by_steap.QueueI32()

q32.push(1)
q32.push(2)
q32.push(3)
q32.push(5)
q32.pop()
q32.pop()
q32.print()


array = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
target = 7

index = steap_by_steap.Binary_search(array, target)
if index is not None:
    print(f"Target {target} found at index {index}")
else:
    print(f"Target {target} not found in the array")


bst = steap_by_steap.BinarySearchTree()
bst.insert(5)
bst.insert(3)
bst.insert(7)

print(bst.search(3))  # Should print True
print(bst.search(6))  # Should print False


arr = [64, 25, 12, 22, 11]
sorted_arr = steap_by_steap.Selection(arr)
print(sorted_arr)  # Output should be [11, 12, 22, 25, 64]



arr = [34, 25, 12, 22, 11]
sorted_arr = steap_by_steap.Insertion(arr)
print(sorted_arr)  # Output should be [11, 12, 22, 25, 34]


arr = [34, 25, 12, 22, 11]
sorted_arr = steap_by_steap.Shell(arr)
print(sorted_arr)  # Output should be [11, 12, 22, 25, 34]


arr = [34, 25, 12, 22, 11]
sorted_arr = steap_by_steap.Quick(arr)
print(sorted_arr)  # Output should be [11, 12, 22, 25, 34]


arr = [34, 25, 12, 22, 11]
sorted_arr = steap_by_steap.Merge(arr)
print(sorted_arr)  # Output should be [11, 12, 22, 25, 34]


data = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
shuffled_data = steap_by_steap.Knuth(data)
print(shuffled_data)


points = [(0.0, 0.0), (1.0, 1.0), (2.0, 2.0), (3.0, 1.0), (0.0, 3.0)]
hull = steap_by_steap.Convex_hull(points)
print(hull)



pq = steap_by_steap.PriorityQueue()
pq.push(4)
pq.push(5)
pq.push(3)
pq.push(10)
print(pq.pop())  # Output: 3
print(pq.pop())  # Output: 5
print(pq.pop())  # Output: 10
print(pq.is_empty())  # Output: True


# Create a B-tree instance
bt = steap_by_steap.BTree(3)

# Insert keys into the B-tree
for key in [10, 20, 5, 6, 12, 30, 7, 17]:
    bt.insert(key)

# Search for a key
print(bt.search(6))  # Output: True
print(bt.search(15))  # Output: False



start_state = steap_by_steap.State(0)
accept_states = [steap_by_steap.State(1)]

nfa = steap_by_steap.NFA(start_state, accept_states)

nfa.add_state(steap_by_steap.State(0))
nfa.add_state(steap_by_steap.State(1))

nfa.add_transition(steap_by_steap.State(0), steap_by_steap.Symbol.char('a'), steap_by_steap.State(1))
nfa.add_transition(steap_by_steap.State(1), steap_by_steap.Symbol.epsilon(), steap_by_steap.State(0))

print(nfa.is_accepted("a"))  # Should print: True
print(nfa.is_accepted("aa")) # Should print: False




pattern = steap_by_steap.Regex("a*b")
print(pattern.is_match("aaab"))  # True
print(pattern.is_match("b"))     # True
print(pattern.is_match("aab"))   # True
print(pattern.is_match("ab"))    # True
print(pattern.is_match("c"))     # False



compressed = steap_by_steap.LZWCompress("TOBEORNOTTOBEORTOBEORNOT")
print("Compressed:", compressed)

decompressed = steap_by_steap.LZWDecompress(compressed)
print("Decompressed:", decompressed)



tableau = [
    [2.0, 3.0, 1.0, 0.0, 0.0, 100.0],
    [4.0, 1.0, 0.0, 1.0, 0.0, 150.0],
    [1.0, 1.0, 0.0, 0.0, 1.0, 50.0],
    [-3.0, -4.0, 0.0, 0.0, 0.0, 0.0]
]

simplex = steap_by_steap.Simplex(tableau)
solution = simplex.solve()
print("Optimal solution:", solution)
