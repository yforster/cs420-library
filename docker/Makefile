DOCKER_COMPOSE = docker-compose
all: build

build: build-base

build-base:
	$(DOCKER_COMPOSE) build base

push:
	$(DOCKER_COMPOSE) up --no-start base
	$(DOCKER_COMPOSE) push base

.PHONY: build run test all build-base
