


type
    BBTree*[K,V] = ref object of RootObj # BBTree is a generic type with keys and values of types K, V
        ## `BBTree` is an opaque immutable type.
    BBLeaf[K,V] = ref object of BBTree
        key:   K                # the search key; must suppprt the generic ``cmp`` proc
        val:   V                # the data value associated with the key, and stored in a node
    BBNode[K,V] = ref object of BBLeaf
        vleft:  BBTree[K,V]      # left subtree; may be nil
        vright: BBTree[K,V]      # right subtree; may be nil
        vsize:  int              # the size of the (sub-)tree rooted in this node

func size[K,V](n: BBLeaf[K,V]):  int = return 1
func left[K,V](n: BBLeaf[K,V]):  BBTree[K,V] = return nil
func right[K,V](n: BBLeaf[K,V]):  BBTree[K,V] = return nil

func size[K,V](n: BBNode[K,V]):  int = return n.vsize
func left[K,V](n: BBNode[K,V]):  BBTree[K,V] = return n.vleft
func right[K,V](n: BBNode[K,V]):  BBTree[K,V] = return n.vright


iterator inorder*[K,V](root: BBTree[K,V]): (K,V) =
    ## Inorder traversal of the tree at `root`, i.e., from smallest to largest key
    # Since recursive iterators are not yet implemented, this uses an explicit stack 
    var stack: seq[BBTree[K,V]] = @[]
    var curr = root
    while (not curr.isNil) or stack.len > 0:
        while (not curr.isNil):
            add(stack, curr) # push node before going left
            curr = curr.left
        # at the leftmost node; curr is nil
        curr = stack.pop()
        yield (curr.key, curr.val)
        curr = curr.right # now go right

# test

func isOrdered[K,V](root: BBTree[K,V], min: K): bool =
    var last = min
    for k,v in inorder(root):
        discard v
        if last == min:
            last = k
        elif cmp(last, k) < 0:
            discard # ok
        else:
            return false
    return true

var root : BBTree[int,int] = nil

assert(isOrdered(root, low(int)))
