# File cACSL/generation/pattern/Makefile

# Run
#  make wp
# for proving.

.PHONY: wp

wp:
	frama-c -wp filtering.c -wp-prover alt-ergo 
	frama-c -wp suffix.c -wp-prover alt-ergo -wp-prop=-soundness
	frama-c -wp allex.c -wp-prover alt-ergo
	frama-c -wp exall.c -wp-prover alt-ergo
	frama-c -wp all2.c -wp-prover alt-ergo
