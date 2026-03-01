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

ci:
	@./scripts/forbid_sorry.sh
	@~/.elan/bin/lake build
	@~/.elan/bin/lake build MoltResearch.Discrepancy.SurfaceChecklist
	@~/.elan/bin/lake build MoltResearch.Discrepancy.DeprecatedSurfaceChecklist

backlog:
	@~/.elan/bin/lake build Tasks
	@~/.elan/bin/lake build Conjectures

task:
	@test -n "$(FILE)" || (echo "FILE is required" && exit 2)
	@./scripts/check_task.sh $(FILE)
