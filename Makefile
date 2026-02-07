.PHONY: build update bootstrap task help

help:
	@echo "Targets:" 
	@echo "  make bootstrap   # first-time setup: lake update + build (requires ~/.elan/bin/lake)"
	@echo "  make update      # lake update"
	@echo "  make build       # lake build"
	@echo "  make task FILE=Tasks/Tier0/T0_07.lean   # run check_task on a task"

bootstrap:
	@./scripts/bootstrap.sh

update:
	@~/.elan/bin/lake update

build:
	@~/.elan/bin/lake build

task:
	@test -n "$(FILE)" || (echo "FILE is required" && exit 2)
	@./scripts/check_task.sh $(FILE)
