#!/bin/bash

time dune exec -- bin/main.exe eval benchmarks/$1/task.ml output/$1.scm
