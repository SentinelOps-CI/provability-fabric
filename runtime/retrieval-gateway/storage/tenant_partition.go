package storage

import (
	"crypto/ed25519"
	"crypto/rand"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"time"
)

// TenantPartition represents a physically partitioned storage for a tenant
type TenantPartition struct {
	TenantID   string          `json:"tenant_id"`
	ShardID    string          `json:"shard_id"`
	Labels     map[string]bool `json:"labels"`
	CreatedAt  time.Time       `json:"created_at"`
	LastAccess time.Time       `json:"last_access"`
}

// PartitionedStorage manages physical partitioning by tenant and label
type PartitionedStorage struct {
	partitions map[string]*TenantPartition
	keys       map[string]ed25519.PrivateKey
}

// NewPartitionedStorage creates a new partitioned storage
func NewPartitionedStorage() *PartitionedStorage {
	return &PartitionedStorage{
		partitions: make(map[string]*TenantPartition),
		keys:       make(map[string]ed25519.PrivateKey),
	}
}

// CreatePartition creates a new physical partition for a tenant
func (ps *PartitionedStorage) CreatePartition(tenantID string, labels []string) (*TenantPartition, error) {
	// Generate shard ID based on tenant and labels
	shardID := ps.generateShardID(tenantID, labels)

	// Generate signing key for this partition
	pubKey, privKey, err := ed25519.GenerateKey(rand.Reader)
	if err != nil {
		return nil, fmt.Errorf("failed to generate signing key: %w", err)
	}

	// Create label map
	labelMap := make(map[string]bool)
	for _, label := range labels {
		labelMap[label] = true
	}

	partition := &TenantPartition{
		TenantID:   tenantID,
		ShardID:    shardID,
		Labels:     labelMap,
		CreatedAt:  time.Now(),
		LastAccess: time.Now(),
	}

	ps.partitions[shardID] = partition
	ps.keys[shardID] = privKey

	return partition, nil
}

// GetPartition retrieves a partition by shard ID
func (ps *PartitionedStorage) GetPartition(shardID string) (*TenantPartition, bool) {
	partition, exists := ps.partitions[shardID]
	if exists {
		partition.LastAccess = time.Now()
	}
	return partition, exists
}

// GetPartitionByTenant retrieves all partitions for a tenant
func (ps *PartitionedStorage) GetPartitionByTenant(tenantID string) []*TenantPartition {
	var partitions []*TenantPartition
	for _, partition := range ps.partitions {
		if partition.TenantID == tenantID {
			partitions = append(partitions, partition)
		}
	}
	return partitions
}

// SignReceipt signs an access receipt for a partition
func (ps *PartitionedStorage) SignReceipt(receipt *AccessReceipt) error {
	partition, exists := ps.partitions[receipt.IndexShard]
	if !exists {
		return fmt.Errorf("partition not found for shard: %s", receipt.IndexShard)
	}

	// Verify tenant matches partition
	if receipt.Tenant != partition.TenantID {
		return fmt.Errorf("tenant mismatch: receipt tenant %s != partition tenant %s",
			receipt.Tenant, partition.TenantID)
	}

	// Create receipt data for signing
	receiptData := map[string]interface{}{
		"receipt_id":  receipt.ReceiptID,
		"tenant":      receipt.Tenant,
		"subject_id":  receipt.SubjectID,
		"query_hash":  receipt.QueryHash,
		"index_shard": receipt.IndexShard,
		"timestamp":   receipt.Timestamp,
		"result_hash": receipt.ResultHash,
	}

	// Serialize and hash the receipt data
	receiptBytes, err := json.Marshal(receiptData)
	if err != nil {
		return fmt.Errorf("failed to marshal receipt: %w", err)
	}

	receiptHash := sha256.Sum256(receiptBytes)

	// Sign the receipt
	privKey := ps.keys[receipt.IndexShard]
	signature := ed25519.Sign(privKey, receiptHash[:])

	// Set receipt signature fields
	receipt.SignAlg = "ed25519"
	receipt.Sig = hex.EncodeToString(signature)

	return nil
}

// VerifyReceipt verifies a signed receipt
func (ps *PartitionedStorage) VerifyReceipt(receipt *AccessReceipt) error {
	partition, exists := ps.partitions[receipt.IndexShard]
	if !exists {
		return fmt.Errorf("partition not found for shard: %s", receipt.IndexShard)
	}

	// Verify tenant matches partition
	if receipt.Tenant != partition.TenantID {
		return fmt.Errorf("tenant mismatch: receipt tenant %s != partition tenant %s",
			receipt.Tenant, partition.TenantID)
	}

	// Recreate receipt data for verification
	receiptData := map[string]interface{}{
		"receipt_id":  receipt.ReceiptID,
		"tenant":      receipt.Tenant,
		"subject_id":  receipt.SubjectID,
		"query_hash":  receipt.QueryHash,
		"index_shard": receipt.IndexShard,
		"timestamp":   receipt.Timestamp,
		"result_hash": receipt.ResultHash,
	}

	// Serialize and hash the receipt data
	receiptBytes, err := json.Marshal(receiptData)
	if err != nil {
		return fmt.Errorf("failed to marshal receipt: %w", err)
	}

	receiptHash := sha256.Sum256(receiptBytes)

	// Decode signature
	signature, err := hex.DecodeString(receipt.Sig)
	if err != nil {
		return fmt.Errorf("invalid signature format: %w", err)
	}

	// Get public key for verification
	pubKey := ps.keys[receipt.IndexShard].Public().(ed25519.PublicKey)

	// Verify signature
	if !ed25519.Verify(pubKey, receiptHash[:], signature) {
		return fmt.Errorf("invalid signature")
	}

	return nil
}

// generateShardID creates a unique shard ID based on tenant and labels
func (ps *PartitionedStorage) generateShardID(tenantID string, labels []string) string {
	data := fmt.Sprintf("%s:%v", tenantID, labels)
	hash := sha256.Sum256([]byte(data))
	return hex.EncodeToString(hash[:8]) // Use first 8 bytes for shorter ID
}

// AccessReceipt represents a signed access receipt
type AccessReceipt struct {
	ReceiptID  string `json:"receipt_id"`
	Tenant     string `json:"tenant"`
	SubjectID  string `json:"subject_id"`
	QueryHash  string `json:"query_hash"`
	IndexShard string `json:"index_shard"`
	Timestamp  int64  `json:"timestamp"`
	ResultHash string `json:"result_hash"`
	SignAlg    string `json:"sign_alg"`
	Sig        string `json:"sig"`
}
