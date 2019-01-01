# Package

version       = "0.1.0"
author        = "Doug Currie"
description   = "Bounded Balance Trees library"
license       = "MIT"
srcDir        = "src"


# Dependencies

requires "nim >= 0.19.0"

# Tasks

task test, "Runs the test suite":
  exec "nim c -r tests/testbbtree.nim"

task moby, "Runs the large test suite":
  exec "nim c --define:STRESS_TEST_N:20000 --define:BB_ITERATIONS:20000 -r tests/testbbtree.nim"

task coverage, "Generate code coverage report":
  echo "Generate code coverage report"
  exec "coco --branch"
