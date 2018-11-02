Using profiling tools
=====================

This document explains the use of standard profiling tools for the development
of Lambdapi.

Using Linux `perf`
------------------

The quickest way to obtain a per-symbol execution time is `perf`. It is simple
to use, provided that you have the right privileges on your machine. No change
is required in the build procedure, but `lambdapi` must be invoked as follows.
```bash
dune exec -- perf record lambdapi [LAMBDAPI_OPTIONS]
```
The program behaves as usual, but a trace is recorded in file `perf.data`. The
data can then be displayed with the following command.
```bash
perf report
```

Profiling using Gprof
---------------------

The `gprof` tool can be used to obtain a more precise (and thorough) execution
trace. However, it requires modifying the `src/dune` file by replacing
```
(executable
 (name lambdapi)
```
with the following.
```
(executable
 (name lambdapi)
 (ocamlopt_flags (:standard -p))
```
This effectively adds the `-p` flag to every invocation of `ocamlopt`.

After doing that, `lambdapi` can be launched on the desired example, to record
an execution trace. This has the (side-)effect of producing a `gmon.out` file.
To retrieve the data, the following command can then be used.
```bash
gprof _build/install/default/lambdapi gmon.out > profile.txt
```
It takes two arguments: the path to the `lambdapi` binary used to generate the
profiling data, and the profiling data itself.
