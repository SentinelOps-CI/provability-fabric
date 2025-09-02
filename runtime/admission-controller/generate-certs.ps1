# Generate self-signed certificate for Admission Controller
$certName = "admission-controller"
$dnsNames = @("admission-controller", "admission-controller.default", "admission-controller.default.svc", "admission-controller.default.svc.cluster.local", "localhost")

# Generate the certificate
$cert = New-SelfSignedCertificate -Subject "CN=$certName" -DnsName $dnsNames -CertStoreLocation "cert:\CurrentUser\My" -KeyUsage DigitalSignature, KeyEncipherment -Type SSLServerAuthentication -NotAfter (Get-Date).AddYears(1)

# Export the certificate to PEM format
$certPath = ".\certs\tls.crt"
$keyPath = ".\certs\tls.key"

# Export certificate
$certBytes = $cert.Export([System.Security.Cryptography.X509Certificates.X509ContentType]::Cert)
$certPem = "-----BEGIN CERTIFICATE-----`n" + [System.Convert]::ToBase64String($certBytes, [System.Base64FormattingOptions]::InsertLineBreaks) + "`n-----END CERTIFICATE-----"
$certPem | Out-File -FilePath $certPath -Encoding ASCII

# Export private key (this is more complex in PowerShell, so we'll create a simple approach)
Write-Host "Certificate generated: $certPath"
Write-Host "Certificate thumbprint: $($cert.Thumbprint)"
Write-Host ""
Write-Host "To export the private key, you can use the following steps:"
Write-Host "1. Open Certificate Manager (certmgr.msc)"
Write-Host "2. Navigate to Personal > Certificates"
Write-Host "3. Find the certificate with thumbprint: $($cert.Thumbprint)"
Write-Host "4. Right-click > All Tasks > Export..."
Write-Host "5. Choose to export the private key and save as .pfx"
Write-Host "6. Convert .pfx to PEM format using OpenSSL or online tools"
Write-Host ""
Write-Host "Alternatively, for development purposes, you can use the certificate file generated at: $certPath"

# For development, create a dummy key file
"-----BEGIN PRIVATE KEY-----`nDUMMY_KEY_FOR_DEVELOPMENT_ONLY`n-----END PRIVATE KEY-----" | Out-File -FilePath $keyPath -Encoding ASCII

Write-Host "Created dummy key file for development at: $keyPath"
Write-Host "For production use, replace with a proper private key."
