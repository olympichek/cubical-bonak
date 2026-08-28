# Parallel builds (`--parallel` / `-j`)

Agda 2.9.0's `--parallel` / `-j` was measured on the full library and
loses to a sequential check: 6 min 42 s against 5 min 34 s. The
module chain `Prelude → … → GpdLemmas → νGpd` is linear, so there is
no module-level parallelism to exploit and the flag only adds
scheduling overhead (cf. agda/agda#8477). Build sequentially.
