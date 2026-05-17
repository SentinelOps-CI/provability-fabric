module github.com/SentinelOps-CI/provability-fabric/tools/pcs-validate

go 1.23

require github.com/SentinelOps-CI/provability-fabric/adapters/pcs v0.0.0

require (
	github.com/google/uuid v1.6.0 // indirect
	github.com/santhosh-tekuri/jsonschema/v5 v5.3.1 // indirect
)

replace github.com/SentinelOps-CI/provability-fabric/adapters/pcs => ../../adapters/pcs
