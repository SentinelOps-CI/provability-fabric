fn main() -> Result<(), Box<dyn std::error::Error>> {
    tonic_build::configure()
        .build_server(true)
        .build_client(true)
        .compile(
            &[
                "../../api/v1/plan.proto",
                "../../api/v1/kernel.proto",
                "../../api/v1/receipt.proto",
                "../../api/v1/egress.proto",
                "../../api/v1/safety_case.proto",
            ],
            &["../../api/v1"],
        )?;
    Ok(())
}
