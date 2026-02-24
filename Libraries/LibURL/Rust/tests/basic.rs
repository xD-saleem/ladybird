use url_lib::UrlBuilder;

#[test]
fn build_basic_url() {
    let url = UrlBuilder::new()
        .scheme("https")
        .host("example.com")
        .push_path("docs")
        .push_path("index.html")
        .build();

    assert_eq!(url.scheme, "https");
    assert_eq!(url.host.unwrap().value, "example.com");
    assert_eq!(url.paths.len(), 2);
}
