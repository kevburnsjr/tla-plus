# Pantopic Config Bus

This spec proposes a lease management protocol that may allow etcd to be vertically partitioned.

In a kubernetes cluster with a lot of nodes, it's not uncommon for lease renewals to account for 66% of all etcd
requests from the kubernetes api server. Splitting etcd's [Lease API](https://etcd.io/docs/v3.5/learning/api/#lease-api)
expiration out of the [Key-Value API](https://etcd.io/docs/v3.5/learning/api/#key-value-api) into separate raft groups may improve its
scalability and efficiency.

This spec will demonstrate a set of properties that are possible to achieve in this sort of arrangement and the
constraints that are necessary to achieve them. The answer to whether this set of properties is sufficient to serve the
needs of etcd's clients given these constraints might very well be yes.

# Constraints

1.