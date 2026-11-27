# Privacy budget guard

The runtime guard uses process-local additive composition over represented
binary64 epsilon and delta costs. The historical MomentsAccountant type name
does not imply a moments-accounting algorithm. The guard rejects missing
tenant configuration, invalid costs, overflow and incomplete parameter pairs.
Charges use conservative upper rounding. Configuration reload replaces the
entire snapshot and clears it on failure; accumulated charges are retained.

This is not a proof of differential privacy. The claimed mechanism costs
must be independently established, and the log observer does not mediate the
underlying operation. Process restart, multiple replicas, explicit resets,
and untrusted input provenance remain outside the enforcement guarantee.
No production deployment should rely on this guard as a durable global
privacy accountant.
