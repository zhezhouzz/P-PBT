#!/bin/bash

time dune exec -- bin/main.exe syn-one benchmarks/$1/task.ml output/$1.scm
