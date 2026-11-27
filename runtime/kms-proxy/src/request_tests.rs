// SPDX-License-Identifier: Apache-2.0
use super::*;
use authority::tests::{fixture_authority, signed_fixture};
use std::sync::atomic::{AtomicUsize, Ordering};

fn proxy(authority: Option<RequestAuthority>) -> KmsProxy {
    KmsProxy { authority, vault_client: None, vault_url: String::new(), vault_token: String::new() }
}

async fn request(proxy: &Arc<KmsProxy>, path: &str, body: Body) -> (StatusCode, serde_json::Value) {
    let response = handle_request(
        Request::post(path).body(body).unwrap(), Arc::clone(proxy)
    ).await.unwrap();
    let status = response.status();
    let bytes = hyper::body::to_bytes(response.into_body()).await.unwrap();
    (status, serde_json::from_slice(&bytes).unwrap())
}

async fn signed(proxy: &Arc<KmsProxy>, value: &KmsRequest) -> (StatusCode, serde_json::Value) {
    request(proxy, "/kms/sign", Body::from(serde_json::to_vec(value).unwrap())).await
}

#[tokio::test]
async fn absent_authority_and_absent_credentials_never_grant_signing() {
    let input = signed_fixture(UtcTimestamp::now());
    let (status, body) = signed(&Arc::new(proxy(None)), &input).await;
    assert_eq!(status, StatusCode::FORBIDDEN);
    assert_eq!(body["success"], false);
    let p = Arc::new(proxy(Some(fixture_authority())));
    let mut absent = input;
    absent.attestation_token = None;
    let (status, body) = signed(&p, &absent).await;
    assert_eq!(status, StatusCode::FORBIDDEN);
    assert!(body["result"].is_null());
}

#[tokio::test]
async fn provider_absence_is_failure_and_cannot_warm_authorization() {
    let p = Arc::new(proxy(Some(fixture_authority())));
    let mut input = signed_fixture(UtcTimestamp::now());
    let (status, body) = signed(&p, &input).await;
    assert_eq!(status, StatusCode::BAD_GATEWAY);
    assert_eq!(body["success"], false);
    assert!(body["result"].is_null());
    input.attestation_token.as_mut().unwrap().signature = "sig_placeholder".into();
    assert_eq!(signed(&p, &input).await.0, StatusCode::FORBIDDEN);
}

#[tokio::test]
async fn unsupported_operations_and_invalid_input_fail_explicitly() {
    let p = Arc::new(proxy(Some(fixture_authority())));
    for path in ["/kms/encrypt", "/kms/decrypt", "/kms/verify", "/kms/rotate-keys"] {
        let (status, body) = request(&p, path, Body::empty()).await;
        assert_eq!(status, StatusCode::NOT_IMPLEMENTED);
        assert_eq!(body["success"], false);
    }
    let (status, _) = request(&p, "/kms/sign", Body::from("{")).await;
    assert_eq!(status, StatusCode::BAD_REQUEST);
    let (status, _) = request(&p, "/kms/sign", Body::from(vec![0; MAX_REQUEST_BODY_BYTES + 1])).await;
    assert_eq!(status, StatusCode::PAYLOAD_TOO_LARGE);
    let mut input = signed_fixture(UtcTimestamp::now());
    input.operation = "decrypt".into();
    assert_eq!(signed(&p, &input).await.0, StatusCode::BAD_REQUEST);
    input.operation = "sign".into();
    input.key_id = "../other".into();
    assert_eq!(signed(&p, &input).await.0, StatusCode::BAD_REQUEST);
}

#[tokio::test]
async fn streaming_bound_checks_accumulated_length() {
    let (mut sender, body) = Body::channel();
    let writer = tokio::spawn(async move {
        sender.send_data(vec![0; MAX_REQUEST_BODY_BYTES].into()).await.unwrap();
        sender.send_data(vec![1].into()).await.unwrap();
    });
    assert_eq!(read_bounded_body(body).await.unwrap_err(), StatusCode::PAYLOAD_TOO_LARGE);
    writer.await.unwrap();
    assert_eq!(read_bounded_body(Body::from(vec![0; MAX_REQUEST_BODY_BYTES])).await.unwrap().len(), MAX_REQUEST_BODY_BYTES);
}

#[tokio::test]
async fn authenticated_provider_transport_and_rejection_controls() {
    let calls = Arc::new(AtomicUsize::new(0));
    let fixture_calls = Arc::clone(&calls);
    let make = make_service_fn(move |_| {
        let calls = Arc::clone(&fixture_calls);
        async move {
            Ok::<_, hyper::Error>(service_fn(move |req: Request<Body>| {
                let calls = Arc::clone(&calls);
                async move {
                    let i = calls.fetch_add(1, Ordering::SeqCst);
                    assert_eq!(req.method(), hyper::Method::POST);
                    assert_eq!(req.uri().path(), "/v1/transit/sign/test-key");
                    assert_eq!(req.headers()["x-vault-token"], "isolated-test-token");
                    let input = hyper::body::to_bytes(req.into_body()).await.unwrap();
                    let input: serde_json::Value = serde_json::from_slice(&input).unwrap();
                    assert_eq!(input["input"], "dGVzdCBtZXNzYWdl");
                    let response = match i {
                        // Synthetic provider response: transport fixture, not a Vault signature proof.
                        0 => json_response(StatusCode::OK, serde_json::json!({"data":{"signature":"vault:v1:ZmFrZQ=="}})),
                        1 => json_response(StatusCode::SERVICE_UNAVAILABLE, serde_json::json!({})),
                        2 => json_response(StatusCode::OK, serde_json::json!({"data":{"signature":"mock_signature_fake"}})),
                        _ => json_response(StatusCode::OK, serde_json::json!({"data":{"signature":"A".repeat(65_537)}})),
                    };
                    Ok::<_, hyper::Error>(response)
                }
            }))
        }
    });
    let server = Server::try_bind(&"127.0.0.1:0".parse().unwrap()).unwrap().serve(make);
    let addr = server.local_addr();
    let task = tokio::spawn(server);
    let mut p = proxy(Some(fixture_authority()));
    p.vault_client = Some(Client::builder().no_proxy().redirect(reqwest::redirect::Policy::none())
        .timeout(std::time::Duration::from_secs(5)).build().unwrap());
    p.vault_url = format!("http://{addr}");
    p.vault_token = "isolated-test-token".into();
    let p = Arc::new(p);

    let (status, body) = signed(&p, &signed_fixture(UtcTimestamp::now())).await;
    assert_eq!(status, StatusCode::OK);
    assert_eq!(body["success"], true);
    assert_eq!(body["result"], "vault:v1:ZmFrZQ==");
    let mut altered = signed_fixture(UtcTimestamp::now());
    altered.data = Some("tampered".into());
    assert_eq!(signed(&p, &altered).await.0, StatusCode::FORBIDDEN);
    altered.attestation_token = None;
    assert_eq!(signed(&p, &altered).await.0, StatusCode::FORBIDDEN);
    assert_eq!(calls.load(Ordering::SeqCst), 1);
    for _ in 0..3 {
        let (status, body) = signed(&p, &signed_fixture(UtcTimestamp::now())).await;
        assert_eq!(status, StatusCode::BAD_GATEWAY);
        assert_eq!(body["success"], false);
        assert!(body["result"].is_null());
    }
    assert_eq!(calls.load(Ordering::SeqCst), 4);
    task.abort();
}

#[test]
fn endpoint_and_key_constraints() {
    for endpoint in ["https://vault.example", "http://127.0.0.1:8200"] {
        assert!(valid_vault_endpoint(endpoint), "{endpoint}");
    }
    for endpoint in ["", "http://vault.example", "https://user:pass@vault.example", "https://vault.example/other", "https://vault.example/?x=1"] {
        assert!(!valid_vault_endpoint(endpoint), "{endpoint}");
    }
    assert!(valid_key_id("test-key_1"));
    for key in ["", "../test", "test/other", "test%2Fother", "test?other", "test#other"] {
        assert!(!valid_key_id(key));
    }
}
