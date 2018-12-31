#[
Copyright (c) 2012-18 Doug Currie, Londonderry, NH, USA

Permission is hereby granted, free of charge, to any person obtaining a copy of this software 
and associated documentation files (the "Software"), to deal in the Software without 
restriction, including without limitation the rights to use, copy, modify, merge, publish, 
distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the 
Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or 
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING 
BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND 
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, 
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, 
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
]#

#[ Bounded Balance Trees a.k.a. Weight Balanced Trees

References:

Implementing Sets Efficiently in a Functional Language
Stephen Adams
CSTR 92-10
Department of Electronics and Computer Science University of Southampton Southampton S09 5NH

Adams’ Trees Revisited Correct and Efficient Implementation
Milan Straka <fox@ucw.cz>
Department of Applied Mathematics Charles University in Prague, Czech Republic
]#

## Bounded Balance Trees a.k.a. Weight Balanced Trees
## 
## a persistent data structure providing a generic (parameterized) key,value map
##
## * Insert (``add``), lookup (``get``), and delete (``del``) in O(log(N)) time
## * Key-ordered iterators (``inorder`` and ``revorder``)
## * Lookup by relative position from beginning or end (``getNth``) in O(log(N)) time
## * Get the position (``rank``) by key in O(log(N)) time
## * Efficient set operations using tree keys
## * Map extensions to set operations with optional value merge control for duplicates

type
    BBTree*[K,V] = ref object   # BBTree is a generic type with keys and values of types K, V
        left:  BBTree[K,V]      # left subtree; may be nil
        right: BBTree[K,V]      # right subtree; may be nil
        size:  int              # the size of the (sub-)tree rooted in this node
        key:   K                # the search key; must suppprt the generic ``cmp`` proc
        val:   V                # the data value associated with the key, and stored in a node

const                           # balance criteria
    omega = 3
    alpha = 2

func nodeSize[K,V](n: BBTree[K,V]): int {.inline.} =
    if n == nil:
        result = 0
    else:
        result = n.size

func len*[K,V](root: BBTree[K,V]): int =
    ## Returns the number of keys in tree at `root`.  O(1)
    result = nodeSize(root)

func newLeaf[K,V](key: K, value: V): BBTree[K,V] =
    # constructor for a leaf node
    result = BBTree[K,V](left: nil, right: nil, size: 1, key: key, val: value)

func newNode[K,V](left: BBTree[K,V], key: K, value: V, right: BBTree[K,V]): BBTree[K,V] =
    # constructor for a new node
    let size = nodeSize(left) + 1 + nodeSize(right)
    result = BBTree[K,V](left: left, right: right, size: size, key: key, val: value)

#[ **************************** balance ********************************
#
singleL l k (Node rl _ rk rr) = node (node l k rl) rk rr
singleR (Node ll _ lk lr) k r = node ll lk (node lr k r)
doubleL l k (Node (Node rll _ rlk rlr) _ rk rr) =
  node (node l k rll) rlk (node rlr rk rr)
doubleR (Node ll _ lk (Node lrl _ lrk lrr)) k r =
  node (node ll lk lrl) lrk (node lrr k r)

balance left key right
    | size left + size right <= 1 = node left key right
    | size right > omega * size left + delta = case right of
         (Node rl _ _ rr) | size rl<alpha*size rr -> singleL left key right
                          | otherwise             -> doubleL left key right
    | size left > omega * size right + delta = case left of
         (Node ll _ _ lr) | size lr<alpha*size ll -> singleR left key right
                          | otherwise             -> doubleR left key right
    | otherwise = node left key right
]#

func singleL[K,V](left: BBTree[K,V], key: K, value: V, right: BBTree[K,V]): BBTree[K,V] =
    result = newNode(newNode(left, key, value, right.left),
                        right.key, 
                        right.val, 
                        right.right)

func doubleL[K,V](left: BBTree[K,V], key: K, value: V, right: BBTree[K,V]): BBTree[K,V] =
    let rl = right.left
    result = newNode(newNode(left, key, value, rl.left),
                     rl.key, 
                     rl.val, 
                     newNode(rl.right, right.key, right.val, right.right))


func singleR[K,V](left: BBTree[K,V], key: K, value: V, right: BBTree[K,V]): BBTree[K,V] =
    result = newNode(left.left,
                     left.key,
                     left.val,
                     newNode(left.right, key, value, right))

func doubleR[K,V](left: BBTree[K,V], key: K, value: V, right: BBTree[K,V]): BBTree[K,V] =
    let lr = left.right
    result = newNode(newNode(left.left, left.key, left.val, lr.left),
                     lr.key,
                     lr.val,
                     newNode(lr.right, key, value, right))

func balance[K,V](left: BBTree[K,V], key: K, value: V, right: BBTree[K,V]): BBTree[K,V] =
    let
        sl = nodeSize(left)
        sr = nodeSize(right)

    if ((sl + sr) <= 1):
        result = newNode(left, key, value, right)
    elif (sr > (omega * sl)):
        if (nodeSize(right.left) < (alpha * nodeSize(right.right))):
            result = singleL(left, key, value, right)
        else:
            result = doubleL(left, key, value, right)
    elif (sl > (omega * sr)):
        if (nodeSize(left.right) < (alpha * nodeSize(left.left))):
            result = singleR(left, key, value, right)
        else:
            result = doubleR(left, key, value, right)
    else:
        result = newNode(left, key, value, right)

#[ **************************** insert ********************************
#
insert :: Ord a => a -> BBTree a -> BBTree a
insert k Nil = node Nil k Nil
insert k (Node left _ key right) = case k ‘compare‘ key of
                                     LT -> balance (insert k left) key right
                                     EQ -> node left k right
                                     GT -> balance left key (insert k right)
]#

func add*[K,V](root: BBTree[K,V], key: K, value: V): BBTree[K,V] =
    ## Returns a new tree with the (`key`, `value`) pair added, or replaced if `key` is already
    ## in the tree `root`. O(log N)
    if root == nil:
        result = newLeaf(key, value)
    else:
        let dif = cmp(key, root.key);
        if (dif < 0):
            result = balance(add(root.left, key, value), root.key, root.val, root.right)
        elif (dif > 0):
            result = balance(root.left, root.key, root.val, add(root.right, key, value))
        else: # key and root.key are equal
            #if (value == root.val)
            #    # no need to allocate a new node
            #    result = node
            #else:
                result = newNode(root.left, key, value, root.right)

#[ ***************************** lookup *********************************
]#

# default is returned is key is not in tree
#
func get*[K,V](root: BBTree[K,V], key: K, default: V): V =
    ## Retrieves the value for `key` in the tree `root` iff `key` is in the tree. 
    ## Otherwise, `default` is returned. O(log N)
    result = default
    var node = root
    while node != nil:
        let dif = cmp(key, node.key)
        if dif < 0:
            node = node.left
        elif dif > 0:
            node = node.right
        else: # key and node.key are eq
            result = node.val
            node = nil # break

func getNth*[K,V](root: BBTree[K,V], index: int, default: (K, V)): (K, V) =
    ## Get the key,value pair of the 0-based `index` key in the tree `root` when index is 
    ## positive and less than the tree length. Or get the tree length plus `index` key in 
    ## the tree `root` when the `index` is negative and greater than the negative tree length.
    ## Otherwise, `default` is returned. O(log N)
    result = default
    let treesize = nodeSize(root)
    var uindex = 0
    var node = root
    if (index < treesize) and (index >= (-treesize)):
        if index < 0:
            uindex = treesize + index # when negative, reverse index from end rather than inorder
        else:
            uindex = index # all set
        while node != nil:
            let leftsize = nodeSize(node.left)
            if uindex < leftsize:
                node = node.left
            elif uindex > leftsize:
                uindex -= (leftsize + 1)
                node = node.right
            else: # we are there!
                result = (node.key, node.val)
                node = nil # break
    # else index is out of range; default is returned

func getMin*[K,V](root: BBTree[K,V], default: (K, V)): (K, V) =
    ## Retrieves the key,value pair with the smallest key in the tree `root`
    ## For an empty tree `default` is returned. O(log N)
    var node = root
    if node == nil:
        result = default
    else:
        while node.left != nil:
            node = node.left;
        result = (node.key, node.val)

func getMax*[K,V](root: BBTree[K,V], default: (K, V)): (K, V) =
    ## Retrieves the key,value pair with the largest key in the tree `root`
    ## For an empty tree `default` is returned. O(log N)
    var node = root
    if node == nil:
        result = default
    else:
        while node.right != nil:
            node = node.right;
        result = (node.key, node.val)

func getKV[K,V](node: BBTree[K,V], default: (K, V)): (K, V) {.inline.} =
    if node == nil:
        result = default
    else:
        result = (node.key, node.val)

func getNext*[K,V](root: BBTree[K,V], key: K, default: (K,V)): (K,V) =
    ## Returns the key,value pair with smallest key > `key`.
    ## It is almost inorder successor, but it also works when `key` is not present.
    ## If there is no such successor key in the tree, `default` is returned. O(log N)
    var last_left_from: BBTree[K,V] = nil
    var node = root
    var done = false
    while not done:
        if node == nil:
            result = getKV(last_left_from, default) # key not found
            done = true
        else:
            let dif = cmp(key, node.key)
            if (dif < 0):
                last_left_from = node
                node = node.left
            elif (dif > 0):
                node = node.right
            else: # key and node.key are eq
                # return value from min node of right subtree, or from last_left_from if none
                if node.right == nil:
                    result = getKV(last_left_from, default)
                else:
                    result = getMin(node.right, default)
                done = true

func getPrev*[K,V](root: BBTree[K,V], key: K, default: (K,V)): (K,V) =
    ## Returns the key,value pair with largest key < `key`.
    ## It is almost inorder predecessor, but it also works when `key` is not present.
    ## If there is no such predecessor key in the tree, `default` is returned. O(log N)
    var last_right_from: BBTree[K,V] = nil
    var node = root
    var done = false
    while not done:
        if node == nil:
            result = getKV(last_right_from, default) # key not found
            done = true
        else:
            let dif = cmp(key, node.key)
            if (dif < 0):
                node = node.left
            elif (dif > 0):
                last_right_from = node
                node = node.right
            else: # key and node.key are eq
                # return value from max node of left subtree, or from last_right_from if none
                if node.left == nil:
                    result = getKV(last_right_from, default)
                else:
                    result = getMax(node.left, default)
                done = true


#[ ***************************** delete *********************************
#
delete :: Ord a => a -> BBTree a -> BBTree a
delete _ Nil = Nil
delete k (Node left _ key right) = case k ‘compare‘ key of
                                     LT -> balance (delete k left) key right
                                     EQ -> glue left right
                                     GT -> balance left key (delete k right)
  where glue Nil right = right
        glue left Nil = left
        glue left right
          | size left > size right = let (key’, left’) = extractMax left
                                     in node left’ key’ right
          | otherwise              = let (key’, right’) = extractMin right
                                     in node left key’ right’
        extractMin (Node Nil _ key right) = (key, right)
        extractMin (Node left _ key right) = case extractMin left of
          (min, left’) -> (min, balance left’ key right)
        extractMax (Node left _ key Nil) = (key, left)
        extractMax (Node left _ key right) = case extractMax right of
          (max, right’) -> (max, balance left key right’)
]#

func extractMin[K,V](node: BBTree[K,V]): (K, V, BBTree[K,V]) = # (mink, minv, node')
    if node.left == nil:
        result = (node.key, node.val, node.right)
    else:
        let (mink, minv, nodep) = extractMin(node.left)
        result = (mink, minv, balance(nodep, node.key, node.val, node.right))

func extractMax[K,V](node: BBTree[K,V]): (K, V, BBTree[K,V]) = # (maxk, maxv, node')
    if node.right == nil:
        result = (node.key, node.val, node.left)
    else:
        let (maxk, maxv, nodep) = extractMax(node.right)
        result = (maxk, maxv, balance(node.left, node.key, node.val, nodep))

func glue[K,V](left: BBTree[K,V], right: BBTree[K,V]): BBTree[K,V] =
    if left == nil:
        result = right
    elif right == nil:
        result = left
    elif nodeSize(left) > nodeSize(right):
        let (maxk, maxv, leftp) = extractMax(left)
        result = newNode(leftp, maxk, maxv, right)
    else:
        let (mink, minv, rightp) = extractMin(right)
        result = newNode(left, mink, minv, rightp)

func del*[K,V](root: BBTree[K,V], key: K): BBTree[K,V] =
    ## Deletes `key` from tree `root`. Does nothing if the key does not exist.
    ## O(log N)
    if root == nil:
        result = root
    else:
        let dif = cmp(key, root.key);
        if (dif < 0):
            result = balance(del(root.left, key), root.key, root.val, root.right)
        elif (dif > 0):
            result = balance(root.left, root.key, root.val, del(root.right, key))
        else: # key and root.key are eq
            result = glue(root.left, root.right)

func delMin*[K,V](root: BBTree[K,V]): BBTree[K,V] =
    ## Delete the minimum element from tree `root`. O(log N)
    if root == nil:
        result = root
    else:
        let (mink, minv, node) = extractMin(root)
        discard mink
        discard minv
        result = node

func delMax*[K,V](root: BBTree[K,V]): BBTree[K,V] =
    ## Delete the maximum element from tree `root`. O(log N)
    if root == nil:
        result = root
    else:
        let (maxk, maxv, node) = extractMax(root)
        discard maxk
        discard maxv
        result = node

#[ ****************************** rank ***********************************
]#

func rank*[K,V](root: BBTree[K,V], key: K, default: int): int =
    ## Retrieves the 0-based index of `key` in the tree `root` iff `key` is in the tree. 
    ## Otherwise, `default` is returned. O(log N)
    result = default
    var n = 0
    var node = root
    while node != nil:
        let dif = cmp(key, node.key);
        if (dif < 0):
            node = node.left
        elif (dif > 0):
            n += 1 + nodeSize(node.left)
            node = node.right
        else: # key and node.key are eq
            result = n + nodeSize(node.left)
            node = nil # break

#[ **************************** iterators ********************************
]#

#[ useless!?...
iterator preorder*[K,V](root: BBTree[K,V]): (K,V) =
  # Preorder traversal of a binary tree.
  # Since recursive iterators are not yet implemented,
  # this uses an explicit stack (which is more efficient anyway):
  var stack: seq[BBTree[K,V]] = @[root]
  while stack.len > 0:
    var curr = stack.pop()
    while curr != nil:
      yield (curr.key, curr.val)
      add(stack, curr.right)  # push right subtree onto the stack
      curr = curr.left        # and follow the left pointer
]#

iterator inorder*[K,V](root: BBTree[K,V]): (K,V) =
  ## Inorder traversal of the tree at `root`, i.e., from smallest to largest key
  # Since recursive iterators are not yet implemented, this uses an explicit stack 
  var stack: seq[BBTree[K,V]] = @[]
  var curr = root
  while curr != nil or stack.len > 0:
    while curr != nil:
        add(stack, curr) # push node before going left
        curr = curr.left
    # at the leftmost node; curr is nil
    curr = stack.pop()
    yield (curr.key, curr.val)
    curr = curr.right # now go right

iterator revorder*[K,V](root: BBTree[K,V]): (K,V) =
  ## Reverse inorder traversal of the tree at `root`, i.e., from largest to smallest key
  # Since recursive iterators are not yet implemented, this uses an explicit stack
  var stack: seq[BBTree[K,V]] = @[]
  var curr = root
  while curr != nil or stack.len > 0:
    while curr != nil:
        add(stack, curr) # push node before going right
        curr = curr.right
    # at the rightmost node; curr is nil
    curr = stack.pop()
    yield (curr.key, curr.val)
    curr = curr.left # now go left


#[ **************************** set operations ********************************
]#

# This is Adams's concat3
#
func join[K,V](key: K, val: V, left, right: BBTree[K,V]): BBTree[K,V] =
    if left == nil:
        result = add(right, key, val)
    elif right == nil:
        result = add(left, key, val)
    else:
        let sl = nodeSize(left)
        let sr = nodeSize(right)
        if (omega * sl) < sr:
            result = balance(join(key, val, left, right.left), right.key, right.val, right.right)
        elif (omega * sr) < sl:
            result = balance(left.left, left.key, left.val, join(key, val, right, left.right))
        else:
            result = newNode(left, key, val, right)

# This is Adams's concat
#
func join[K,V](left, right: BBTree[K,V]): BBTree[K,V] =
    if left == nil:
        result = right
    elif right == nil:
        result =left
    else:
        let (key, val, rightp) = extractMin(right)
        result = join(key, val, left, rightp)

# This is Adams's split_lt and split_gt combined into one function, along with contains(root, key)
#
func split[K,V](key: K, root: BBTree[K,V]): (BBTree[K,V], bool, BBTree[K,V]) =
    if root == nil:
        result = (root, false, root)
    else:
        let dif = cmp(key, root.key)
        if dif < 0:
            let (l, b, r) = split(key, root.left)
            result = (l, b, join(root.key, root.val, r, root.right))
        elif dif > 0:
            let (l, b, r) = split(key, root.right)
            result = (join(root.key, root.val, root.left, l), b, r)
        else: # key and node.key are eq
            result = (root.left, true, root.right)

func splitMerge[K,V](key: K, val: V, root: BBTree[K,V], merge: func (k: K, v1, v2: V): V): 
    (BBTree[K,V], bool, V, BBTree[K,V]) =
    if root == nil:
        result = (root, false, val, root)
    else:
        let dif = cmp(key, root.key)
        if dif < 0:
            let (l, b, val, r) = splitMerge(key, val, root.left, merge)
            result = (l, b, val, join(root.key, root.val, r, root.right))
        elif dif > 0:
            let (l, b, val, r) = splitMerge(key, val, root.right, merge)
            result = (join(root.key, root.val, root.left, l), b, val, r)
        else: # key and node.key are eq
            result = (root.left, true, merge(key, val, root.val), root.right)

func union*[K,V](tree1, tree2: BBTree[K,V]): BBTree[K,V] =
    ## Returns the union of the sets represented by the keys in `tree1` and `tree2`.
    ## When viewed as maps, returns the key,value pairs that appear in either tree; if
    ## a key appears in both trees, the value for that key is selected from `tree1`, so
    ## this function is asymmetrical for maps. If you need more comtrol over how the 
    ## values are selected for duplicate keys, see `unionMerge`. O(M + N) but if the minimum
    ## key of one tree is greater than the maximum key of the other tree then O(log M) 
    ## where M is the size of the larger tree.
    if tree1 == nil:
        result = tree2
    elif tree2 == nil:
        result = tree1
    else:
        let (l, b, r) = split(tree1.key, tree2)
        discard b
        result = join(tree1.key, tree1.val, union(tree1.left, l), union(tree1.right, r))

func unionMerge*[K,V](tree1, tree2: BBTree[K,V], merge: func (k: K, v1, v2: V): V): BBTree[K,V] =
    ## Returns the union of the sets represented by the keys in `tree1` and `tree2`.
    ## When viewed as maps, returns the key,value pairs that appear in either tree; if
    ## a key appears in both trees, the value for that key is the result of the supplied
    ## `merge` function, which is passed the common key, and the values from `tree1` and 
    ## `tree2` respectively.  O(M + N) but if the minimum
    ## key of one tree is greater than the maximum key of the other tree then O(log M) 
    ## where M is the size of the larger tree.
    if tree1 == nil:
        result = tree2
    elif tree2 == nil:
        result = tree1
    else:
        let (l, b, v, r) = splitMerge(tree1.key, tree1.val, tree2, merge)
        discard b
        result = join(tree1.key, v, unionMerge(tree1.left, l, merge), unionMerge(tree1.right, r, merge))

func difference*[K,V](tree1, tree2: BBTree[K,V]): BBTree[K,V] =
    ## Returns the asymmetric set difference between `tree1` and `tree2`. In other words, 
    ## returns the keys that are in `tree1`, but not in `tree2`.  O(M + N)
    if tree1 == nil or tree2 == nil:
        result = tree1
    else:
        let (l, b, r) = split(tree2.key, tree1)
        discard b
        result = join(difference(l, tree2.left), difference(r, tree2.right))

func symmetricDifference*[K,V](tree1, tree2: BBTree[K,V]): BBTree[K,V] =
    ## Returns the symmetric set difference between `tree1` and `tree2`. In other words, 
    ## returns the keys that are in `tree1`, but not in `tree2`, union the keys that are in 
    ## `tree2` but not in `tree1`.  O(M + N)
    if tree1 == nil:
        result = tree2
    if tree2 == nil:
        result = tree1
    else:
        let (l, b, r) = split(tree2.key, tree1)
        if b:
            result = join(symmetricDifference(l, tree2.left), symmetricDifference(r, tree2.right))
        else:
            result = join(tree1.key, tree1.val, symmetricDifference(l, tree2.left), symmetricDifference(r, tree2.right))

func contains*[K,V](root: BBTree[K,V], key: K): bool =
    ## Returns `true` if the `key` is in the tree `root`
    ## otherwise `false`. O(log N)
    result = false
    var node = root
    while node != nil:
        let dif = cmp(key, node.key)
        if dif < 0:
            node = node.left
        elif dif > 0:
            node = node.right
        else: # key and node.key are eq
            result = true
            node = nil # break

func intersection*[K,V](tree1, tree2: BBTree[K,V]): BBTree[K,V] =
    ## Returns the set intersection of `tree1` and `tree2`. In other words, returns the keys
    ## that are in both trees. 
    ## When viewed as maps, returns the key,value pairs for keys that appear in both trees; 
    ## the value each key is selected from `tree1`, so
    ## this function is asymmetrical for maps. If you need more comtrol over how the 
    ## values are selected for duplicate keys, see `uintersectionMerge`. O(M + N)
    if tree1 == nil:
        result = tree1
    if tree2 == nil:
        result = tree2
    else:
        let (l, b, r) = split(tree1.key, tree2)
        if b:
            result = join(tree1.key, tree1.val, intersection(tree1.left, l), intersection(tree1.right, r))
        else:
            result = join(intersection(tree1.left, l), intersection(tree1.right, r))

func intersectionMerge*[K,V](tree1, tree2: BBTree[K,V], merge: func (k: K, v1, v2: V): V): BBTree[K,V] =
    ## Returns the set intersection of `tree1` and `tree2`. In other words, returns the keys
    ## that are in both trees. 
    ## When viewed as maps, returns the key,value pairs for keys that appear in both trees; 
    ## the value for each key is the result of the supplied
    ## `merge` function, which is passed the common key, and the values from `tree1` and 
    ## `tree2` respectively.  O(M + N)
    if tree1 == nil:
        result = tree1
    if tree2 == nil:
        result = tree2
    else:
        let (l, b, v, r) = splitMerge(tree1.key, tree2, merge)
        if b:
            result = join(tree1.key, v, intersectionMerge(tree1.left, l, merge), intersectionMerge(tree1.right, r, merge))
        else:
            result = join(intersectionMerge(tree1.left, l, merge), intersectionMerge(tree1.right, r, merge))

func isSubset*[K,V](tree1, tree2: BBTree[K,V]): bool =
    ## Returns true iff the keys in `tree1` form a subset of the keys in `tree2`. In other words, 
    ## if all the keys that are in `tree1` are also in `tree2`. O(N) where N is `len(tree1)`
    ## Use `isProperSubset` instead to determins that there are keys in `tree2` that are not in `tree1`.
    if tree1 == nil:
        result = true
    elif len(tree1) > len(tree2):
        result = false
    else:
        # tree2 is not nil or else the above length test would have been true
        let dif = cmp(tree1.key, tree2.key)
        if dif < 0:
            result = isSubset(tree1.left, tree2.left) and
                     tree2.contains(tree1.key) and
                     isSubset(tree1.right, tree2)
        elif dif > 0:
            result = isSubset(tree1.right, tree2.right) and
                     tree2.contains(tree1.key) and 
                     isSubset(tree1.left, tree2)
        else: # tree1.key and tree2.key are eq
            result = isSubset(tree1.left, tree2.left) and isSubset(tree1.right, tree2.right)

func disjoint*[K,V](tree1, tree2: BBTree[K,V]): bool =
    ## Returns true iff `tree1` and `tree2` have no keys in common. O(N) where N is
    ## `len(tree1)`
    result = true # default
    if tree1 != nil and tree2 != nil:
        let dif = cmp(tree1.key, tree2.key)
        if dif < 0:
            if not disjoint(tree1.left, tree2.left): return false
            if tree2.contains(tree1.key): return false
            return disjoint(tree1.right, tree2)
        elif dif > 0:
            if not disjoint(tree1.right, tree2.right): return false
            if tree2.contains(tree1.key): return false 
            return disjoint(tree1.left, tree2)
        else: # tree1.key and tree2.key are eq
            return false

func isProperSubset*[K,V](tree1, tree2: BBTree[K,V]): bool =
    ## Returns true iff the keys in `tree1` form a proper subset of the keys in `tree2`. 
    ## In other words, if all the keys that are in `tree1` are also in `tree2`, but there are 
    ## keys in `tree2` that are not in `tree1`.  O(N) where N is `len(tree1)`
    result = isSubset(tree1, tree2) and len(tree1) < len(tree2)

func `+`*[K,V](s1, s2: BBTree[K,V]): BBTree[K,V] {.inline.} =
    ## Alias for `union(s1, s2) <#union>`_.
    result = union(s1, s2)

func `*`*[K,V](s1, s2: BBTree[K,V]): BBTree[K,V] {.inline.} =
    ## Alias for `intersection(s1, s2) <#intersection>`_.
    result = intersection(s1, s2)

func `-`*[K,V](s1, s2: BBTree[K,V]): BBTree[K,V] {.inline.} =
    ## Alias for `difference(s1, s2) <#difference>`_.
    result = difference(s1, s2)

# A -+- B  ==  (A - B) + (B - A)  ==  (A + B) - (A * B)

func `-+-`*[K,V](s1, s2: BBTree[K,V]): BBTree[K,V] {.inline.} =
    ## Alias for `symmetricDifference(s1, s2) <#symmetricDifference>`_.
    result = symmetricDifference(s1, s2)

func `<`*[K,V](s1, s2: BBTree[K,V]): bool {.inline.} =
    ## Alias for `isProperSubset(s1, s2) <#isProperSubset>`_.
    ## Returns true if the keys in `s1` form a strict or proper subset of the keys in `s2`.
    ##
    ## A strict or proper subset `s1` has all of its keys in `s2` but `s2` has
    ## more elements than `s1`.
    result = isProperSubset(s1, s2)

func `<=`*[K,V](s1, s2: BBTree[K,V]): bool {.inline.} =
    ## Alias for `isSubset(s1, s2) <#isSubset>`_.
    ## Returns true if `s1` is subset of `s2`.
    ##
    ## A subset `s1` has all of its members in `ts2` and `s2` doesn't necessarily
    ## have more members than `s1`. That is, `s1` can be equal to `s2`.
    result = isSubset(s1, s2)

#[
#  `==` seems like an extreme assertion when values are not being considered...
#  Furhtermore, it messes up all the tests for `== nil` above turning them into infinite regress
#
func `==`*[K,V](s1, s2: BBTree[K,V]): bool {.inline.} =
    ## Returns true if both `s1` and `s2` have the same keys and set size.
    result = isSubset(s1, s2) and len(s1) == len(s2)
]#

#[ **************************** for unit tests ********************************
]#

func countKeys*[K,V](root: BBTree[K,V]): int =
    ## Used for unit testing only; normally use `len` to get the number of keys.
    var node = root
    result = 0
    while node != nil:
        result += countKeys(node.left)
        result += 1
        node = node.right

func balanced[K,V](node: BBTree[K,V]): int = # returns size in nodes or -1 for error
    if node == nil:
        return 0
    let
        sl = nodeSize(node.left)
        sr = nodeSize(node.right)
        sz = nodeSize(node)
    if sz != (sl + 1 + sr):
        # fprintf(stderr, "Error in bbwatree balanced: %u != %u + 1 + %u; (%u %u)\n", sz, sl, sr, nx->left, nx->right);
        return -1
    if (sl + sr) <= 1:
        # balanced
        discard
    elif sr > (omega * sl):
        # fprintf(stderr, "Error in bbwatree balanced: sr %u > omega * %u\n", sr, sl);
        return -1
    elif sl > (omega * sr):
        # fprintf(stderr, "Error in bbwatree balanced: sl %u > omega * %u\n", sl, sr);
        return -1
    let
        slb = balanced(node.left)
        srb = balanced(node.right)
    if (slb < 0) or (sl != slb):
        # if (slb >= 0) fprintf(stderr, "Error in bbwatree balanced: sl %u != %lld\n", sl, slb);
        return -1
    if (srb < 0) or (sr != srb):
        # if (srb >= 0) fprintf(stderr, "Error in bbwatree balanced: sr %u != %lld\n", sr, srb);
        return -1
    return sz

func isBalanced*[K,V](root: BBTree[K,V]): bool =
    ## Used for unit testing only; returns `true` if the tree is balanced, which should always
    ## be the case.
    let size = balanced(root)
    if root == nil:
        return (size == 0)
    return (size > 0) and (size == nodeSize(root))

#[ ***************************** sanity check ********************************
]#

when isMainModule:

    proc test1() =
        var
            tre0 : BBTree[string,int] = nil
            tre1 = add(tre0, "hello", 1) # instantiate a BBTree with ("hello",1)
            tre2 = add(tre1, "world", 1) # add ("world",2)
        for str,num in inorder(tre2):
            stdout.writeLine(str)
    test1()
    echo "done"


#[ ******************************** notes ***********************************

## For a bbwa tree, the max depth is log2(n) / log2(1 + 1/ω)
## With omega at 3, log2(1 + 1/ω) = log2(1 + 1/3) = 0.41503749927884
## The upper bound on depth is 2.41 * log2(n)

]#