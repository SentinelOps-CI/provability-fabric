// SPDX-License-Identifier: Apache-2.0

//! UTC timestamp wire contract for the MPC demonstration.
//!
//! The supported domain is RFC 3339 years 0000–9999, with nanosecond
//! precision and no leap-second aliases. Emit the legacy UTC spelling
//! (Z and 0, 3, 6 or 9 fractional digits) for supported values.
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use time::{format_description::well_known::Rfc3339, OffsetDateTime};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct UtcTimestamp(OffsetDateTime);

impl UtcTimestamp {
    pub fn now() -> Self {
        Self(OffsetDateTime::now_utc())
    }

    pub fn from_timestamp(seconds: i64, nanos: u32) -> Option<Self> {
        if nanos >= 1_000_000_000 {
            return None;
        }
        let total = i128::from(seconds) * 1_000_000_000 + i128::from(nanos);
        let utc = OffsetDateTime::from_unix_timestamp_nanos(total).ok()?;
        (0..=9999).contains(&utc.year()).then_some(Self(utc))
    }

    pub fn timestamp(self) -> i64 {
        self.0.unix_timestamp()
    }

    /// Preserve Chrono's legacy explicit UTC offset in audit hash inputs.
    pub fn legacy_offset_wire(self) -> Option<String> {
        self.wire().map(|wire| format!("{}+00:00", wire.trim_end_matches('Z')))
    }

    pub fn checked_add_hours(self, hours: i64) -> Option<Self> {
        let seconds = hours.checked_mul(3600)?;
        let next = self.0.checked_add(time::Duration::seconds(seconds))?;
        Self::from_timestamp(next.unix_timestamp(), next.nanosecond())
    }

    /// UTC display for the demonstration's millisecond-resolution logs.
    pub fn clock_time_millis(self) -> String {
        format!("{:02}:{:02}:{:02}.{:03}", self.0.hour(), self.0.minute(), self.0.second(), self.0.millisecond())
    }

    pub fn parse(input: &str) -> Option<Self> {
        // Reject leap seconds and sub-nanosecond precision explicitly;
        // a parser that normalizes either would change the claimed instant.
        let bytes = input.as_bytes();
        if bytes.get(17..19) == Some(b"60") {
            return None;
        }
        if bytes.get(19) == Some(&b'.') {
            let precision = bytes[20..].iter().take_while(|b| b.is_ascii_digit()).count();
            if precision > 9 {
                return None;
            }
        }
        let value = OffsetDateTime::parse(input, &Rfc3339).ok()?;
        Self::from_timestamp(value.unix_timestamp(), value.nanosecond())
    }

    fn wire(self) -> Option<String> {
        let value = self.0;
        if !(0..=9999).contains(&value.year()) {
            return None;
        }
        let mut result = format!(
            "{:04}-{:02}-{:02}T{:02}:{:02}:{:02}",
            value.year(), value.month() as u8, value.day(),
            value.hour(), value.minute(), value.second()
        );
        let nanos = value.nanosecond();
        if nanos == 0 {
            // Whole seconds use the legacy spelling with no decimal point.
        } else if nanos.is_multiple_of(1_000_000) {
            result.push_str(&format!(".{:03}", nanos / 1_000_000));
        } else if nanos.is_multiple_of(1_000) {
            result.push_str(&format!(".{:06}", nanos / 1_000));
        } else {
            result.push_str(&format!(".{:09}", nanos));
        }
        result.push('Z');
        Some(result)
    }
}

impl Serialize for UtcTimestamp {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let wire = self.wire().ok_or_else(|| {
            serde::ser::Error::custom("UTC timestamp outside the supported wire domain")
        })?;
        serializer.serialize_str(&wire)
    }
}

impl<'de> Deserialize<'de> for UtcTimestamp {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let wire = String::deserialize(deserializer)?;
        Self::parse(&wire).ok_or_else(|| {
            serde::de::Error::custom("invalid or unsupported RFC 3339 timestamp")
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn preserves_legacy_fractional_utc_spelling() {
        for (nanos, suffix) in [
            (0, "Z"), (100_000_000, ".100Z"), (1_000_000, ".001Z"),
            (123_450_000, ".123450Z"), (1_000, ".000001Z"),
            (123_456_789, ".123456789Z"), (1, ".000000001Z"),
        ] {
            let value = UtcTimestamp::from_timestamp(1_700_000_000, nanos).unwrap();
            let expected = format!("\"2023-11-14T22:13:20{suffix}\"");
            assert_eq!(serde_json::to_string(&value).unwrap(), expected);
            assert_eq!(serde_json::from_str::<UtcTimestamp>(&expected).unwrap(), value);
        }
    }

    #[test]
    fn normalizes_offsets_and_preserves_pre_epoch_seconds() {
        let value = UtcTimestamp::parse("1970-01-01T01:00:00.100+01:00").unwrap();
        assert_eq!(value.timestamp(), 0);
        assert_eq!(value.wire().unwrap(), "1970-01-01T00:00:00.100Z");
        let before = UtcTimestamp::parse("1969-12-31T23:59:59.999999999Z").unwrap();
        assert_eq!(before.timestamp(), -1);
        assert_eq!(before.legacy_offset_wire().unwrap(), "1969-12-31T23:59:59.999999999+00:00");
    }

    #[test]
    fn preserves_explicit_offset_and_checked_compliance_deadline() {
        let value = UtcTimestamp::parse("2023-11-14T23:13:20.100+01:00").unwrap();
        assert_eq!(value.legacy_offset_wire().unwrap(), "2023-11-14T22:13:20.100+00:00");
        assert_eq!(value.clock_time_millis(), "22:13:20.100");
        assert_eq!(value.checked_add_hours(24).unwrap().timestamp() - value.timestamp(), 86400);
        assert!(value.checked_add_hours(i64::MAX).is_none());
        assert!(UtcTimestamp::parse("9999-12-31T23:59:59Z").unwrap().checked_add_hours(1).is_none());
    }

    #[test]
    fn rejects_unrepresentable_and_lossy_claims() {
        for seconds in [i64::MIN, i64::MAX, -62_167_219_201, 253_402_300_800] {
            assert!(UtcTimestamp::from_timestamp(seconds, 0).is_none());
        }
        assert!(UtcTimestamp::from_timestamp(0, 1_000_000_000).is_none());
        for input in [
            "2016-12-31T23:59:60Z", "2023-11-14T22:13:20.1234567891Z",
            "2023-02-30T00:00:00Z", "2023-11-14T22:13:20",
            "0000-01-01T00:00:00+01:00", "9999-12-31T23:59:59-01:00",
        ] {
            assert!(UtcTimestamp::parse(input).is_none(), "{input}");
        }
        for input in ["0000-01-01T00:00:00Z", "9999-12-31T23:59:59Z"] {
            assert_eq!(UtcTimestamp::parse(input).unwrap().wire().unwrap(), input);
        }
    }
}
