//! Field elements as they appear in a proof's public inputs: 32 bytes each,
//! big endian, concatenated.

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct FieldElement(pub [u8; 32]);

impl FieldElement {
    pub fn from_u64(value: u64) -> Self {
        let mut out = [0u8; 32];

        out[24..].copy_from_slice(&value.to_be_bytes());

        Self(out)
    }

    /// Reads a field element as an integer, refusing anything that does not
    /// fit, so a caller can never silently truncate a value it compares.
    pub fn to_u64(self) -> Result<u64, Error> {
        if self.0[..24].iter().any(|byte| *byte != 0) {
            return Err(Error::ValueTooLarge);
        }

        let mut tail = [0u8; 8];

        tail.copy_from_slice(&self.0[24..]);

        Ok(u64::from_be_bytes(tail))
    }

    pub fn is_zero(self) -> bool {
        self.0.iter().all(|byte| *byte == 0)
    }

    pub fn to_hex(self) -> String {
        self.0.iter().map(|byte| format!("{byte:02x}")).collect()
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    ValueTooLarge,
    MalformedPublicInputs { length: usize },
    MissingPublicInput { index: usize, available: usize },
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ValueTooLarge => write!(f, "field element does not fit in 64 bits"),
            Self::MalformedPublicInputs { length } => {
                write!(f, "public inputs are {length} bytes, not a multiple of 32")
            }
            Self::MissingPublicInput { index, available } => {
                write!(
                    f,
                    "public input {index} requested but only {available} present"
                )
            }
        }
    }
}

impl std::error::Error for Error {}

pub fn parse_public_inputs(bytes: &[u8]) -> Result<Vec<FieldElement>, Error> {
    if !bytes.len().is_multiple_of(32) {
        return Err(Error::MalformedPublicInputs {
            length: bytes.len(),
        });
    }

    Ok(bytes
        .chunks_exact(32)
        .map(|chunk| {
            let mut element = [0u8; 32];

            element.copy_from_slice(chunk);

            FieldElement(element)
        })
        .collect())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_trips_small_integers() {
        assert_eq!(FieldElement::from_u64(42).to_u64(), Ok(42));

        assert_eq!(FieldElement::from_u64(0).to_u64(), Ok(0));

        assert_eq!(FieldElement::from_u64(u64::MAX).to_u64(), Ok(u64::MAX));
    }

    #[test]
    fn refuses_to_truncate() {
        let mut wide = [0u8; 32];

        wide[0] = 1;

        assert_eq!(FieldElement(wide).to_u64(), Err(Error::ValueTooLarge));
    }

    #[test]
    fn parses_a_concatenated_vector() {
        let mut bytes = Vec::new();

        bytes.extend_from_slice(&FieldElement::from_u64(1).0);

        bytes.extend_from_slice(&FieldElement::from_u64(2).0);

        let parsed = parse_public_inputs(&bytes).unwrap();

        assert_eq!(parsed.len(), 2);

        assert_eq!(parsed[1].to_u64(), Ok(2));
    }

    #[test]
    fn rejects_a_truncated_vector() {
        assert_eq!(
            parse_public_inputs(&[0u8; 40]),
            Err(Error::MalformedPublicInputs { length: 40 })
        );
    }
}
