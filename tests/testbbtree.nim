
import unittest, random, strutils, times
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

suite "test opacity bbtree.nim":

    var root : BBTree[int,string] = nil

    root = add(root, 1, "one")

    test "opacity":
        # manually checked, generate compile errors as expected...
        # check(root.left == false)
        # check(root.right == false)
        # check(root.size == false)
        # check(root.key == false)
        # check(root.val == false)
        discard


suite "test map and fold bbtree.nim":

    var root : BBTree[int,int] = nil
    #let null = root 

    for i in 1..<20:
        root = add(root, i, -i)

    test "fold to string":
        var d = fold(root, 
                    proc (k: int, v: int, b: string): string = discard k; $v & ";" & b,
                    "")
        # echo d
        let s = split(d, {';'})
        var i = 0
        for k,v in inorder(root):
            check($v == s[i])
            i += 1
            discard k

    test "map to string":
        let t2 = map(root,
                    proc (k: int, v: int): string = $k & ":" & $v)
        check(t2.len == root.len)
        # check(t2 == root) # set == just checks keys, but typecheck fails
        check(t2 <= root)
        check(root <= t2)
        for k,v in revorder(t2):
            check(root.contains(k))
            check(k in root) # alt syntax using `in` template
            check(v.is(string))
            let s = split(v, {':'})
            check($k == s[0])
            check($(-k) == s[1])
        for k,v in revorder(root):
            check(t2.contains(k))
            check(v.is(int))

suite "test set funcs of bbtree.nim":

    test "toSet":
       var numbers : BBTree[int,bool] = toSet([1, 2, 3, 4, 5])
       check(numbers.contains(2))
       check(numbers.contains(4))

    test "Nim compat":
        var
            a : BBTree[string,bool] = toSet(["a", "b"])
            b : BBTree[string,bool] = toSet(["b", "c"])
            c = union(a, b)
        # `==` not working yet, so check twice, <= and >=
        check(c =?= toSet(["a", "b", "c"]))
        var d = intersection(a, b)
        check(d =?= toSet(["b"]))
        var e = difference(a, b)
        check(e =?= toSet(["a"]))
        var f = symmetricDifference(a, b)
        check(f =?= toSet(["a", "c"]))
        check(d < a and d < b)
        check((a < a) == false)
        check(d <= a and d <= b)
        check((a <= a))
        # Alias test.
        check(a + b =?= toSet(["a", "b", "c"]))
        check(a * b =?= toSet(["b"]))
        check(a - b =?= toSet(["a"]))
        check(a -+- b =?= toSet(["a", "c"]))
        check(disjoint(a, b) == false)
        check(disjoint(a, b - a) == true)

    test "Pairs as keys":
        type pair = tuple[a, b: int]
        var aa : BBTree[pair,bool]
        var bb : BBTree[pair,bool]
        var x = (a:1,b:2)
        var y = (a:3,b:4)
        aa = aa.add(x, true)
        aa = aa.add(y, true)
        bb = bb.add(x, true)
        bb = bb.add(y, true)
        check(aa =?= bb)

    test "ints as set keys":
        var aa : BBTree[int,bool]
        for i in 1..99: aa = aa.add(i, true)
        var bb : BBTree[int,bool]
        for i in 33..131: bb = bb.add(i, true)
        var cc = aa * bb
        check(len(cc) == 67)
        check(len(cc - aa) == 0)
        check(len(cc - bb) == 0)
        check(len(aa + bb) == 131)
        check(len(bb + aa) == 131)
        #echo len(aa - bb)
        #echo fold((aa - bb), proc (k: int, v: bool, b: string): string = discard v; $k & ";" & b, "")
        check(len(aa - bb) == 32)
        check(len(bb - aa) == 32)
        check(len(aa -+- bb) == 64)
        check(len(bb -+- aa) == 64)
        #let dd = (aa -+- bb)
        # echo fold(dd, proc (k: int, v: bool, b: string): string = discard v; $k & ";" & b, "")
        #for k,v in inorder(bb -+- aa):
        #    check(k in dd)
        check((bb -+- aa) =?= (aa -+- bb))
        check((bb + aa) =?= (aa + bb))
        check((bb * aa) =?= (aa * bb))
        check(disjoint(bb * aa, aa -+- bb))

suite "random stress test of bbtree.nim":

    const
        STRESS_TEST_N {.intdefine.} : int = 2000
        BB_ITERATIONS {.intdefine.} : int = 2000

        MARKER = low(int64)
        chs = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"

    var
        tree : BBTree[string, int64]
        intree : array[0..STRESS_TEST_N-1, int64]
        qintree = 0
        q_ins = 0
        q_del = 0
        rand1 : Rand

    proc init_random_tree() =
        rand1 = initRand(0x987654321)
        for i in 0..<STRESS_TEST_N:
            intree[i] = MARKER
        qintree = 0;
        q_ins = 0
        q_del = 0

    proc make_random_key_val(k: int64) : (string, int64) =
        var randk = initRand(k)
        let size = rand(randk, 16) + 8
        var key = repeat(' ', size)
        for i in 0..<size:
            key[i] = chs[rand(randk,51)]
        result = (key, -k)

    proc tstput(k: int64) =
        let (key,val) = make_random_key_val(k)
        tree = tree.add(key, val)

    proc tstget(k: int64) : int64 =
        let (key,val) = make_random_key_val(k)
        discard val
        result = tree.get(key, 1)

    proc tstrem(k: int64) =
        let (key,val) = make_random_key_val(k)
        discard val
        tree = tree.del(key)

    proc do_random_tree_op()  =
        let x = rand(rand1, STRESS_TEST_N-1)
        let n = intree[x]
        if n == MARKER:
            # insert
            let k = rand(rand1, high(int64))
            tstput(k)
            intree[x] = k
            qintree += 1
            q_ins += 1
        else:
            # delete
            tstrem(n)
            intree[x] = MARKER
            qintree -= 1
            q_del += 1

    proc find_and_wipe_duplicate() : int =
        result = 0
        for i in 0..<STRESS_TEST_N:
            let n = intree[i]
            if n != MARKER:
                for j in (i+1)..<STRESS_TEST_N:
                    if n == intree[j]:
                        # duplicate
                        intree[j] = MARKER
                        qintree -= 1
                        q_ins -= 1
                        return j # > 0

    test "timed random tree iterations":
        var stop = false
        var start = cpuTime()
        init_random_tree()
        for i in 1..BB_ITERATIONS:
            if stop: break
            do_random_tree_op()
            for j in 0..<STRESS_TEST_N:
                let n = intree[j]
                if n != MARKER:
                    let v = tstget(n)
                    check(v <= 0)
                    check(v == -n)
                    if v == 1:
                        stop = true
                        break
            let sz = tree.len
            if sz != q_ins - q_del:
                let dup = find_and_wipe_duplicate()
                if dup != 0:
                    # whew!
                    echo "dup!"
            check(sz == (q_ins - q_del))
            if stop or (sz != (q_ins - q_del)):
                #fprintf(stderr, "random err: %u nodes, %ld final size\n", sz, q_ins - q_del);
                check(not stop)
                stop = true
            if i mod 1024 == 0:
                write(stderr, ".")
                check(isOrdered(tree, ""))
                check(isBalanced(tree))
        let finish = cpuTime()
        #echo "CPU time [s] ", finish - start, " for ", BB_ITERATIONS, " ops, averaging ", (finish - start) / BB_ITERATIONS
        write(stderr, "\nCPU time [s] ", finish - start,
                      " for ", BB_ITERATIONS, " ops, averaging ",
                       (finish - start) / toFloat(BB_ITERATIONS), " s per op\n")
        write(stderr, "random q: ", q_ins, " inserts, ", q_del, " deletes, ", qintree, " qintree, ", q_ins - q_del, " final size\n")


#[

]#

#    test "out of bounds error is thrown on bad access":
#        let v = @[1, 2, 3]  # you can do initialization here
#        expect(IndexError):
#            discard v[4]
  
    # echo "suite teardown"
