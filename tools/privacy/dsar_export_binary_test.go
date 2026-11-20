package main

import (
	"archive/zip"
	"bytes"
	"crypto"
	_ "crypto/sha256"
	"io"
	"os"
	"path/filepath"
	"testing"

	"golang.org/x/crypto/openpgp"
	"golang.org/x/crypto/openpgp/packet"
	"golang.org/x/crypto/openpgp/armor"
)

// TestDSAREncryptionUsesBinaryLiteralPacket guards the wire-format contract:
// encrypted ZIP files must remain binary, even if they contain CRLF and other
// bytes a text-mode OpenPGP recipient might translate.
func TestDSAREncryptionUsesBinaryLiteralPacket(t *testing.T) {
	keyConfig := &packet.Config{DefaultHash: crypto.SHA256}
	recipient, err := openpgp.NewEntity("DSAR fixture", "", "dsar@example.invalid", keyConfig)
	if err != nil {
		t.Fatalf("generate disposable OpenPGP recipient: %v", err)
	}
	// NewEntity sets the hash preference after initial signing. Re-sign before
	// public serialization to persist a verifiable SHA-256 preference.
	if err := recipient.SerializePrivate(io.Discard, keyConfig); err != nil {
		t.Fatalf("finalize disposable recipient signatures: %v", err)
	}

	var publicKey bytes.Buffer
	armoredKey, err := armor.Encode(&publicKey, openpgp.PublicKeyType, nil)
	if err != nil {
		t.Fatalf("armor disposable public key: %v", err)
	}
	if err := recipient.Serialize(armoredKey); err != nil {
		_ = armoredKey.Close()
		t.Fatalf("serialize disposable public key: %v", err)
	}
	if err := armoredKey.Close(); err != nil {
		t.Fatalf("finalize disposable public key: %v", err)
	}

	dir := t.TempDir()
	keyPath := filepath.Join(dir, "recipient.asc")
	if err := os.WriteFile(keyPath, publicKey.Bytes(), 0600); err != nil {
		t.Fatalf("write disposable public key: %v", err)
	}

	var archive bytes.Buffer
	zipWriter := zip.NewWriter(&archive)
	member, err := zipWriter.Create("dsar-data.json")
	if err != nil {
		t.Fatalf("create ZIP member: %v", err)
	}
	payload := []byte{'{', '"', 'x', '"', ':', '"', 'a', '\r', '\n', 0x00, 0xff, '"', '}'}
	n, err := member.Write(payload)
	if err != nil || n != len(payload) {
		t.Fatalf("write binary ZIP fixture: wrote %d of %d: %v", n, len(payload), err)
	}
	if err := zipWriter.Close(); err != nil {
		t.Fatalf("finalize binary ZIP fixture: %v", err)
	}

	archivePath := filepath.Join(dir, "export.zip")
	want := archive.Bytes()
	if err := os.WriteFile(archivePath, want, 0600); err != nil {
		t.Fatalf("write plaintext binary ZIP fixture: %v", err)
	}

	exporter := DSARExporter{publicKeyPath: keyPath}
	if err := exporter.encryptFile(archivePath); err != nil {
		t.Fatalf("encrypt binary ZIP fixture: %v", err)
	}
	encrypted, err := os.ReadFile(archivePath)
	if err != nil {
		t.Fatalf("read encrypted ZIP: %v", err)
	}
	block, err := armor.Decode(bytes.NewReader(encrypted))
	if err != nil {
		t.Fatalf("decode encrypted OpenPGP armor: %v", err)
	}
	if block.Type != "PGP MESSAGE" {
		t.Fatalf("unexpected encrypted packet armor type %q", block.Type)
	}
	message, err := openpgp.ReadMessage(block.Body, openpgp.EntityList{recipient}, nil, nil)
	if err != nil {
		t.Fatalf("decrypt disposable OpenPGP message: %v", err)
	}
	if message.LiteralData == nil || !message.LiteralData.IsBinary {
		t.Fatal("ZIP content must be encoded as an OpenPGP binary literal-data packet")
	}
	got, err := io.ReadAll(message.UnverifiedBody)
	if err != nil {
		t.Fatalf("consume authenticated OpenPGP payload: %v", err)
	}
	if message.SignatureError != nil {
		t.Fatalf("OpenPGP integrity verification failed: %v", message.SignatureError)
	}
	if !bytes.Equal(got, want) {
		t.Fatalf("decrypted ZIP bytes differ from original (got %d, want %d)", len(got), len(want))
	}
}
