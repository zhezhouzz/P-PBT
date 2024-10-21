#!/bin/bash

time dune exec -- bin/main.exe compile-to-p benchmarks/$1/task.ml output/$1.scm benchmarks/$1/pheader.ml penv/$1/PSyn/SynClient.p
