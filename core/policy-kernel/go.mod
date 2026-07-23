module policykernel

go 1.21

require (
	github.com/alicebob/miniredis/v2 v2.33.0
	github.com/go-redis/redis/v8 v8.11.5
	github.com/provability-fabric/core/crypto/dsse v0.0.0
)

require (
	github.com/alicebob/gopher-json v0.0.0-20200520072559-a9ecdc9d1d3a // indirect
	github.com/cespare/xxhash/v2 v2.2.0 // indirect
	github.com/dgryski/go-rendezvous v0.0.0-20200823014737-9f7001d12a5f // indirect
	github.com/fsnotify/fsnotify v1.7.0 // indirect
	github.com/onsi/gomega v1.29.0 // indirect
	github.com/yuin/gopher-lua v1.1.1 // indirect
	golang.org/x/sys v0.15.0 // indirect
	golang.org/x/text v0.14.0 // indirect
)

replace github.com/provability-fabric/core/crypto/dsse => ../crypto/dsse
