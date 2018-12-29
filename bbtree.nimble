# Package

version       = "0.1.0"
author        = "Doug Currie"
description   = "Bounded Balance Trees library"
license       = "MIT"
srcDir        = "src"


# Dependencies

requires "nim >= 0.19.0"

# Tasks

task coverage, "Generate code coverage report":
  echo "Generate code coverage report"
  exec "coco --branch"
