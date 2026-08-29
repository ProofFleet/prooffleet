.PHONY: build update bootstrap task backlog help ci

help:
	@echo "Targets:" 
	@echo "  make bootstrap   # first-time setup: lake update + build (requires ~/.elan/bin/lake)"
	@echo "  make update      # lake update"
	@echo "  make build       # lake build (verified artifacts)"
	@echo "  make ci          # run forbid_sorry script then lake build"
	@echo "  make backlog     # build Tasks + Conjectures libs (backlog)"
	@echo "  make task FILE=Tasks/Tier0/T0_07.lean   # run check_task on a task"

bootstrap:
	@./scripts/bootstrap.sh

update:
	@~/.elan/bin/lake update

build:
	@~/.elan/bin/lake build

# Mirrors .github/workflows/ci.yml: one lake invocation covering the canonical
# CI target set (default lib + standalone audit/regression modules + Solutions
# + the Tasks/Conjectures backlog), plus both forbid scripts.
# The target list itself lives in scripts/ci_targets.txt so this recipe and the
# workflow cannot drift apart.
CI_TARGETS = $(shell grep -vE '^[[:space:]]*(\#|$$)' scripts/ci_targets.txt | tr '\n' ' ')

ci:
	@./scripts/forbid_sorry.sh
	@./scripts/forbid_axiom_unsafe.sh
	@test -n "$(strip $(CI_TARGETS))" || (echo "ERROR: no targets in scripts/ci_targets.txt" && exit 1)
	@~/.elan/bin/lake build $(CI_TARGETS)

backlog:
	@~/.elan/bin/lake build Tasks
	@~/.elan/bin/lake build Conjectures

task:
	@test -n "$(FILE)" || (echo "FILE is required" && exit 2)
	@./scripts/check_task.sh $(FILE)
