
import unittest, random
import bbtree

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


suite "test int,int bbtree.nim":

    # echo "suite setup"

    var root : BBTree[int,int] = nil
    let null = root 

    var rand0 : Rand = initRand(0x987654321)
  
    setup:
        # echo "run before each test"
        discard
  
    teardown:
        # echo "run after each test"
        discard
  
    test "empty tree is ordered, balanced, has length zero":
        # give up and stop if this fails
        require(isOrdered(root, low(int)))
        check(isBalanced(root))
        check(len(root) == 0)

    test "one entry tree is ordered, balanced, has length one":
        root = add(root, 1, -1)
        check(isOrdered(root, low(int)))
        check(isBalanced(root))
        check(len(root) == 1)

    test "one entry tree lookup works":
        var res = get(root, 1, -42)
        check(res == -1)
        res = get(root, 3, -42)
        check(res == -42)
        check(isOrdered(root, low(int)))
        check(isBalanced(root))
        check(len(root) == 1)

    test "add items in increasing key order, check ordered, balanced, has length 21":
        for i in 2..<22:
            root = add(root, i, -i)
        check(isOrdered(root, low(int)))
        check(isBalanced(root))
        check(len(root) == 21)

    test "add items in decreasing key order, check ordered, balanced, has length 44":
        for i in (-44)..(-22):
            root = add(root, -i, i)
        check(isOrdered(root, low(int)))
        check(isBalanced(root))
        check(len(root) == 44)

    test "check that some items are in the length 44 tree":
        let (mk,mv) = getMin(root,(-99,99))
        check(mk == 1 and mv == -1)
        let (xk,xv) = getMax(root,(-99,99))
        check(xk == 44 and xv == -44)
        let av = get(root, 25, 500)
        check(av == -25)
        let (nk,nv) = getNth(root,6,(-99,99)) # nth is 0-based
        check(nk == 7 and nv == -7)
        let (pk,pv) = getNth(root,-7,(-99,99)) # -1 is last
        check(pk == 38 and pv == -38)
        let (k0,v0) = getMin(null,(-99,99))
        check(k0 == -99 and v0 == 99)
        let (k1,v1) = getMax(null,(-99,99))
        check(k1 == -99 and v1 == 99)
        check(isOrdered(root, low(int)))
        check(isBalanced(root))
        check(len(root) == 44)
        let (ek,ev) = getNth(root,98,(-99,99)) # off the end
        check(ek == -99 and ev == 99)
        let (bk,bv) = getNth(root,-77,(-88,88)) # off the end
        check(bk == -88 and bv == 88)

    test "check succ and pred functions in the length 44 tree":
        let (k1,v1) = getNext(root,3,(-99,99))
        check(k1 == 4 and v1 == -4)
        let (k2,v2) = getPrev(root,22,(-99,99))
        check(k2 == 21 and v2 == -21)
        let (k3,v3) = getPrev(root,1,(-99,99))
        check(k3 == -99 and v3 == 99)
        let (k4,v4) = getNext(root,low(int),(-99,99))
        check(k4 == 1 and v4 == -1)
        let (k5,v5) = getPrev(root,100,(-99,99))
        check(k5 == 44 and v5 == -44)
        check(isOrdered(root, low(int)))
        check(isBalanced(root))
        check(len(root) == 44)
        check(countKeys(root) == 44)
        check(rank(root,1,-99) == 0)
        for i in 2..44:
            check(rank(root,i,-99) == i-1)
        # for code coverage...
        for i in 2..45:
            let (k,v) = getPrev(root,i,(-99,99))
            check(k == i-1 and v == -(i-1))
        for i in 0..43:
            let (k,v) = getNext(root,i,(-99,99))
            check(k == i+1 and v == -(i+1))

    test "delete some items, check, check ordered, balanced, and length":
        root = del(root, 13)
        check(isOrdered(root, low(int)))
        check(isBalanced(root))
        check(len(root) == 43)
        var res = get(root, 13, -999)
        check(res == -999)
        res = get(root, 26, -999)
        check(res == -26)
        root = del(root, 26)
        check(isOrdered(root, low(int)))
        check(isBalanced(root))
        check(len(root) == 42)
        res = get(root, 26, -999)
        check(res == -999)
        res = get(root, 1, -999)
        check(res == -1)
        root = delMin(root)
        check(isOrdered(root, low(int)))
        check(isBalanced(root))
        check(len(root) == 41)
        res = get(root, 1, -999)
        check(res == -999)
        res = get(root, 44, -999)
        check(res == -44)
        root = delMax(root)
        check(isOrdered(root, low(int)))
        check(isBalanced(root))
        check(len(root) == 40)
        res = get(root, 44, -999)
        check(res == -999)
        check(delMin(null) == nil)
        check(delMax(null) == nil)
        check(del(null, 19) == nil)

    test "delete random items, check, check ordered, balanced, and length":
        var n = len(root)
        while n > 0:
            let i = rand(rand0, n-1)
            let (k0,v0) = getNth(root,i,(-99,99))
            discard v0
            check(k0 != -99)
            root = del(root, k0)
            let v1 = get(root,k0,99)
            check(v1 == 99)
            n = n-1
            check(len(root) == n)
            check(isOrdered(root, low(int)))
            check(isBalanced(root))

    test "using add to replace values":
        for i in 1..9:
            root = add(root, i, -i)
        check(isOrdered(root, low(int)))
        check(isBalanced(root))
        check(len(root) == 9)
        check(get(root,3,99) == -3)
        root = add(root, 3, -33)
        check(len(root) == 9)
        check(get(root,3,99) == -33)



#    test "out of bounds error is thrown on bad access":
#        let v = @[1, 2, 3]  # you can do initialization here
#        expect(IndexError):
#            discard v[4]
  
    # echo "suite teardown"
