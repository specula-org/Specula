module github.com/specula/etcd-trace-generator

go 1.23

// Default replace path is updated at runtime by Specula's pipeline.
replace go.etcd.io/raft/v3 => ../../../../../output/etcd/raft_workspace

require go.etcd.io/raft/v3 v3.0.0-00010101000000-000000000000

require (
	github.com/gogo/protobuf v1.3.2 // indirect
	github.com/golang/protobuf v1.5.4 // indirect
	google.golang.org/protobuf v1.33.0 // indirect
)
