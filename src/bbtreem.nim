#[
Copyright (c) 2012-19 Doug Currie, Londonderry, NH, USA

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

const                           # balance criteria
    omega = 3
    alpha = 2

type
    BBTree*[K,V] = ref object of RootObj # BBTree is a generic type with keys and values of types K, V
        ## `BBTree` is an opaque immutable type.
    BBLeaf[K,V] = ref object of BBTree[K,V]
        vkey:   K               # the search key; must support the generic ``cmp`` proc
        vval:   V               # the data value associated with the key, and stored in a node
    BBNode[K,V] = ref object of BBTree[K,V]
        vkey:   K               # the search key; must support the generic ``cmp`` proc
        vval:   V               # the data value associated with the key, and stored in a node
        vleft:  BBTree[K,V]     # left subtree; may be nil
        vright: BBTree[K,V]     # right subtree; may be nil
        vsize:  int             # the size of the (sub-)tree rooted in this node

method key[K,V](n: BBTree[K,V]): K {.base.} = discard
method val[K,V](n: BBTree[K,V]): V {.base.} = discard
method size[K,V](n: BBTree[K,V]): int {.base.} = return 357
method left[K,V](n: BBTree[K,V]): BBTree[K,V] {.base.} = discard
method right[K,V](n: BBTree[K,V]): BBTree[K,V] {.base.} = discard

method key[K,V](n: BBLeaf[K,V]): K = n.vkey
method val[K,V](n: BBLeaf[K,V]): V = n.vval
method size[K,V](n: BBLeaf[K,V]): int = return 1
method left[K,V](n: BBLeaf[K,V]): BBTree[K,V] = discard
method right[K,V](n: BBLeaf[K,V]): BBTree[K,V] = discard

method key[K,V](n: BBNode[K,V]): K = n.vkey
method val[K,V](n: BBNode[K,V]): V = n.vval
method size[K,V](n: BBNode[K,V]):  int = return n.vsize
method left[K,V](n: BBNode[K,V]):  BBTree[K,V] = return n.vleft
method right[K,V](n: BBNode[K,V]):  BBTree[K,V] = return n.vright

func nodeSize[K,V](n: BBTree[K,V]): int {.inline.} =
    if n.isNil:
        result = 0
    else:
        result = n.size

func len*[K,V](root: BBTree[K,V]): int =
    ## Returns the number of keys in tree at `root`.  O(1)
    result = nodeSize(root)

func newLeaf[K,V](key: K, value: V): BBTree[K,V] =
    # constructor for a leaf node
    result = BBLeaf[K,V](vkey: key, vval: value)

func newNode[K,V](left: BBTree[K,V], key: K, value: V, right: BBTree[K,V]): BBTree[K,V] =
    # constructor for a new node
    if left.isNil and right.isNil:
        result = BBLeaf[K,V](vkey: key, vval: value)
    else:
        let size = nodeSize(left) + 1 + nodeSize(right)
        result = BBNode[K,V](vleft: left, vright: right, vsize: size, vkey: key, vval: value)

func singleL[K,V](aleft: BBTree[K,V], akey: K, avalue: V, aright: BBTree[K,V]): BBTree[K,V] =
    result = newNode(newNode(aleft, akey, avalue, aright.left),
                        aright.key, 
                        aright.val, 
                        aright.right)

func doubleL[K,V](aleft: BBTree[K,V], akey: K, avalue: V, aright: BBTree[K,V]): BBTree[K,V] =
    let rl = aright.left
    result = newNode(newNode(aleft, akey, avalue, rl.left),
                     rl.key, 
                     rl.val, 
                     newNode(rl.right, aright.key, aright.val, aright.right))

func singleR[K,V](aleft: BBTree[K,V], akey: K, avalue: V, aright: BBTree[K,V]): BBTree[K,V] =
    result = newNode(aleft.left,
                     aleft.key,
                     aleft.val,
                     newNode(aleft.right, akey, avalue, aright))

func doubleR[K,V](aleft: BBTree[K,V], akey: K, avalue: V, aright: BBTree[K,V]): BBTree[K,V] =
    let lr = aleft.right
    result = newNode(newNode(aleft.left, aleft.key, aleft.val, lr.left),
                     lr.key,
                     lr.val,
                     newNode(lr.right, akey, avalue, aright))

func balance[K,V](aleft: BBTree[K,V], key: K, value: V, aright: BBTree[K,V]): BBTree[K,V] =
    let
        sl = nodeSize(aleft)
        sr = nodeSize(aright)
    if ((sl + sr) <= 1):
        result = newNode(aleft, key, value, aright)
    elif (sr > (omega * sl)):
        if (nodeSize(aright.left) < (alpha * nodeSize(aright.right))):
            result = singleL(aleft, key, value, aright)
        else:
            result = doubleL(aleft, key, value, aright)
    elif (sl > (omega * sr)):
        if (nodeSize(aleft.right) < (alpha * nodeSize(aleft.left))):
            result = singleR(aleft, key, value, aright)
        else:
            result = doubleR(aleft, key, value, aright)
    else:
        result = newNode(aleft, key, value, aright)

func add*[K,V](root: BBTree[K,V], keyy: K, value: V): BBTree[K,V] =
    ## Returns a new tree with the (`keyy`, `value`) pair added, or replaced if `keyy` is already
    ## in the tree `root`. O(log N)
    if root.isNil:
        result = newLeaf[K,V](keyy, value)
    else:
        let dif = cmp(keyy, root.key);
        if (dif < 0):
            result = balance(add(root.left, keyy, value), root.key, root.val, root.right)
        elif (dif > 0):
            result = balance(root.left, root.key, root.val, add(root.right, keyy, value))
        else: # key and root.key are equal
            result = newNode(root.left, keyy, value, root.right)

when isMainModule:
    proc test1() =
        var
            tre0 : BBTree[string,int] = nil
            tre1 = add(tre0, "hello", 1) # instantiate a BBTree with ("hello",1)
            tre2 = add(tre1, "world", 1) # add ("world",2)
            int0 : BBTree[int,int] = nil
            int1 = add(int0, 1, 1) # instantiate a BBTree with (1,1)
            int2 = add(int1, 2, 2) # add (2,2)
        assert(len(int2) == 2)
    test1()
    echo "done"
