#[cfg(feature = "profiling")]
pub type Guard = hotpath::HotpathGuard;

#[cfg(not(feature = "profiling"))]
pub struct Guard;

#[cfg(feature = "profiling")]
pub fn start_from_env() -> Option<Guard> {
    if !env_flag("DEXDEC_PROFILE") {
        return None;
    }

    Some(
        hotpath::HotpathGuardBuilder::new("dexdec")
            .functions_limit(80)
            .threads_limit(0)
            .sections(vec![hotpath::Section::FunctionsTiming])
            .build(),
    )
}

#[cfg(not(feature = "profiling"))]
pub fn start_from_env() -> Option<Guard> {
    if env_flag("DEXDEC_PROFILE") {
        eprintln!(
            "DEXDEC_PROFILE is set, but dexdec was built without `--features profiling`; profiling is disabled."
        );
    }
    None
}

#[cfg(feature = "profiling")]
#[macro_export]
macro_rules! profile_scope {
    ($label:literal, $body:block) => {{
        let mut __dexdec_profile_run = || $body;
        hotpath::measure_block!($label, __dexdec_profile_run())
    }};
    ($label:literal, $body:expr) => {{
        hotpath::measure_block!($label, $body)
    }};
}

#[cfg(not(feature = "profiling"))]
#[macro_export]
macro_rules! profile_scope {
    ($label:literal, $body:block) => {{
        let _ = $label;
        let mut __dexdec_profile_run = || $body;
        __dexdec_profile_run()
    }};
    ($label:literal, $body:expr) => {{
        let _ = $label;
        $body
    }};
}

fn env_flag(name: &str) -> bool {
    std::env::var(name)
        .map(|value| {
            let value = value.trim();
            value == "1"
                || value.eq_ignore_ascii_case("true")
                || value.eq_ignore_ascii_case("yes")
                || value.eq_ignore_ascii_case("on")
        })
        .unwrap_or(false)
}
