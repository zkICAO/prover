//! Where each value sits in a circuit's public inputs.
//!
//! Barretenberg lays them out as the public parameters in declaration order
//! followed by the return values, so the indices below follow the circuit
//! signatures.
//!
//! Those signatures live in another repository, which means this table can
//! drift from them silently. `layout.manifest` at the root of this crate is
//! the guard: it is generated from the compiled ABIs, committed here, and
//! checked by the tests at the end of this file. A signature change that is
//! not reflected in a regenerated manifest fails those tests.

use crate::field::{Error, FieldElement};

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Circuit {
    Sod,
    DgExtract,
    Attributes,
    Compare,
    Member,
    Reveal,
    Nullifier,
    AnchorInclusion,
    AnchorChain,
}

impl Circuit {
    pub fn name(self) -> &'static str {
        match self {
            Self::Sod => "sod",
            Self::DgExtract => "dg_extract",
            Self::Attributes => "attributes",
            Self::Compare => "predicate_compare",
            Self::Member => "predicate_member",
            Self::Reveal => "predicate_reveal",
            Self::Nullifier => "nullifier",
            Self::AnchorInclusion => "anchor_inclusion",
            Self::AnchorChain => "anchor_chain",
        }
    }

    pub fn public_input_count(self) -> usize {
        match self {
            Self::Sod => 5,
            Self::DgExtract => 5,
            Self::Attributes => 5,
            Self::Compare => 6,
            Self::Member => 5,
            Self::Reveal => 9,
            Self::Nullifier => 5,
            Self::AnchorInclusion => 4,
            Self::AnchorChain => 5,
        }
    }

    /// Index of `domain`, which every circuit carries and which must agree
    /// across a bundle.
    pub fn domain_index(self) -> usize {
        match self {
            Self::Sod => 0,
            Self::DgExtract => 2,
            Self::Attributes => 2,
            Self::Compare => 4,
            Self::Member => 3,
            Self::Reveal => 7,
            Self::Nullifier => 2,
            Self::AnchorInclusion => 1,
            Self::AnchorChain => 2,
        }
    }

    /// Index of `context`, which scopes a proof to one session.
    pub fn context_index(self) -> usize {
        self.domain_index() + 1
    }
}

pub struct PublicInputs {
    pub circuit: Circuit,
    values: Vec<FieldElement>,
}

impl PublicInputs {
    pub fn new(circuit: Circuit, values: Vec<FieldElement>) -> Result<Self, Error> {
        let expected = circuit.public_input_count();

        if values.len() != expected {
            return Err(Error::MissingPublicInput {
                index: expected - 1,
                available: values.len(),
            });
        }

        Ok(Self { circuit, values })
    }

    pub fn at(&self, index: usize) -> Result<FieldElement, Error> {
        self.values
            .get(index)
            .copied()
            .ok_or(Error::MissingPublicInput {
                index,
                available: self.values.len(),
            })
    }

    pub fn domain(&self) -> Result<FieldElement, Error> {
        self.at(self.circuit.domain_index())
    }

    pub fn context(&self) -> Result<FieldElement, Error> {
        self.at(self.circuit.context_index())
    }

    // sod: domain, context, econtent_binding, dsc_commitment, secret_binding
    pub fn sod_econtent_binding(&self) -> Result<FieldElement, Error> {
        self.expect(Circuit::Sod)?;

        self.at(2)
    }

    pub fn sod_dsc_commitment(&self) -> Result<FieldElement, Error> {
        self.expect(Circuit::Sod)?;

        self.at(3)
    }

    pub fn sod_secret_binding(&self) -> Result<FieldElement, Error> {
        self.expect(Circuit::Sod)?;

        self.at(4)
    }

    // dg_extract: dg_number, econtent_binding, domain, context, dg_binding
    pub fn dg_number(&self) -> Result<FieldElement, Error> {
        self.expect(Circuit::DgExtract)?;

        self.at(0)
    }

    pub fn dg_extract_econtent_binding(&self) -> Result<FieldElement, Error> {
        self.expect(Circuit::DgExtract)?;

        self.at(1)
    }

    pub fn dg_extract_dg_binding(&self) -> Result<FieldElement, Error> {
        self.expect(Circuit::DgExtract)?;

        self.at(4)
    }

    // attributes: dg_binding, current_yyyymmdd, domain, context, commitment
    pub fn attributes_dg_binding(&self) -> Result<FieldElement, Error> {
        self.expect(Circuit::Attributes)?;

        self.at(0)
    }

    pub fn attributes_current_date(&self) -> Result<FieldElement, Error> {
        self.expect(Circuit::Attributes)?;

        self.at(1)
    }

    pub fn attributes_commitment(&self) -> Result<FieldElement, Error> {
        self.expect(Circuit::Attributes)?;

        self.at(4)
    }

    /// The commitment a predicate or the nullifier was proved against.
    pub fn referenced_commitment(&self) -> Result<FieldElement, Error> {
        match self.circuit {
            Circuit::Compare | Circuit::Member | Circuit::Reveal => self.at(1),
            Circuit::Nullifier => self.at(0),
            other => Err(unexpected(other)),
        }
    }

    pub fn field_id(&self) -> Result<FieldElement, Error> {
        match self.circuit {
            Circuit::Compare | Circuit::Member | Circuit::Reveal => self.at(0),
            other => Err(unexpected(other)),
        }
    }

    pub fn nullifier_secret_binding(&self) -> Result<FieldElement, Error> {
        self.expect(Circuit::Nullifier)?;

        self.at(1)
    }

    // Both anchor modes publish the trusted set first and the commitment
    // last: inclusion carries registry_root, domain, context, commitment, and
    // the chain mode carries master_list_root, current_yyyymmdd, domain,
    // context, commitment.
    pub fn anchor_registry_root(&self) -> Result<FieldElement, Error> {
        match self.circuit {
            Circuit::AnchorInclusion | Circuit::AnchorChain => self.at(0),
            other => Err(unexpected(other)),
        }
    }

    /// The chain mode carries the date it checked certificate validity
    /// against; the inclusion mode checks no validity and carries none.
    pub fn anchor_current_date(&self) -> Result<FieldElement, Error> {
        self.expect(Circuit::AnchorChain)?;

        self.at(1)
    }

    pub fn anchor_dsc_commitment(&self) -> Result<FieldElement, Error> {
        match self.circuit {
            Circuit::AnchorInclusion => self.at(3),
            Circuit::AnchorChain => self.at(4),
            other => Err(unexpected(other)),
        }
    }

    pub fn nullifier_value(&self) -> Result<FieldElement, Error> {
        self.expect(Circuit::Nullifier)?;

        self.at(4)
    }

    fn expect(&self, circuit: Circuit) -> Result<(), Error> {
        if self.circuit == circuit {
            Ok(())
        } else {
            Err(unexpected(self.circuit))
        }
    }
}

fn unexpected(circuit: Circuit) -> Error {
    Error::MissingPublicInput {
        index: circuit.public_input_count(),
        available: circuit.public_input_count(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const ALL: [Circuit; 9] = [
        Circuit::Sod,
        Circuit::DgExtract,
        Circuit::Attributes,
        Circuit::Compare,
        Circuit::Member,
        Circuit::Reveal,
        Circuit::Nullifier,
        Circuit::AnchorInclusion,
        Circuit::AnchorChain,
    ];

    fn inputs(circuit: Circuit) -> PublicInputs {
        let values = (0..circuit.public_input_count())
            .map(|index| FieldElement::from_u64(index as u64))
            .collect();

        PublicInputs::new(circuit, values).unwrap()
    }

    #[test]
    fn context_always_follows_domain() {
        for circuit in ALL {
            let public = inputs(circuit);

            let domain = public.domain().unwrap().to_u64().unwrap();

            let context = public.context().unwrap().to_u64().unwrap();

            assert_eq!(context, domain + 1, "{}", circuit.name());
        }
    }

    #[test]
    fn every_index_is_within_the_declared_count() {
        for circuit in ALL {
            let public = inputs(circuit);

            assert!(public.context().is_ok(), "{}", circuit.name());

            assert!(
                public.at(circuit.public_input_count()).is_err(),
                "{}",
                circuit.name()
            );
        }
    }

    #[test]
    fn a_wrong_length_vector_is_rejected() {
        let short = vec![FieldElement::from_u64(0); 2];

        assert!(PublicInputs::new(Circuit::Sod, short).is_err());
    }

    #[test]
    fn accessors_refuse_the_wrong_circuit() {
        assert!(inputs(Circuit::Compare).sod_secret_binding().is_err());

        assert!(inputs(Circuit::Sod).nullifier_value().is_err());

        assert!(inputs(Circuit::Sod).field_id().is_err());
    }

    /// Maps a compiled circuit package name onto the kind this crate knows.
    fn kind_of(package: &str) -> Option<Circuit> {
        if package.starts_with("sod_") {
            Some(Circuit::Sod)
        } else if package.starts_with("dg_extract_") {
            Some(Circuit::DgExtract)
        } else if package.starts_with("attributes_") {
            Some(Circuit::Attributes)
        } else if package == "predicate_compare" {
            Some(Circuit::Compare)
        } else if package == "predicate_member" {
            Some(Circuit::Member)
        } else if package == "predicate_reveal" {
            Some(Circuit::Reveal)
        } else if package.starts_with("nullifier_") {
            Some(Circuit::Nullifier)
        } else if package.starts_with("anchor_dsc_inclusion") {
            Some(Circuit::AnchorInclusion)
        } else if package.starts_with("anchor_csca_chain") {
            Some(Circuit::AnchorChain)
        } else {
            None
        }
    }

    fn manifest() -> Vec<(Circuit, Vec<String>)> {
        let raw = include_str!("../layout.manifest");

        raw.lines()
            .filter(|line| !line.starts_with('#') && !line.trim().is_empty())
            .filter_map(|line| {
                let mut parts = line.split_whitespace();

                let package = parts.next()?;

                let names = parts.map(str::to_string).collect();

                kind_of(package).map(|circuit| (circuit, names))
            })
            .collect()
    }

    #[test]
    fn the_manifest_covers_every_circuit_kind() {
        let seen: Vec<Circuit> = manifest().into_iter().map(|(c, _)| c).collect();

        for circuit in ALL {
            assert!(
                seen.contains(&circuit),
                "{} missing from manifest",
                circuit.name()
            );
        }
    }

    #[test]
    fn declared_counts_match_the_compiled_circuits() {
        for (circuit, names) in manifest() {
            assert_eq!(
                circuit.public_input_count(),
                names.len(),
                "{} declares {} public inputs but the compiled circuit has {}",
                circuit.name(),
                circuit.public_input_count(),
                names.len()
            );
        }
    }

    #[test]
    fn domain_and_context_sit_where_this_crate_reads_them() {
        for (circuit, names) in manifest() {
            assert_eq!(
                names[circuit.domain_index()],
                "domain",
                "{} reads domain from the wrong index",
                circuit.name()
            );

            assert_eq!(
                names[circuit.context_index()],
                "context",
                "{} reads context from the wrong index",
                circuit.name()
            );
        }
    }

    #[test]
    fn named_values_sit_where_this_crate_reads_them() {
        for (circuit, names) in manifest() {
            let public = inputs(circuit);

            let index_of = |value: &FieldElement| value.to_u64().unwrap() as usize;

            match circuit {
                Circuit::Sod => {
                    assert_eq!(
                        names[index_of(&public.sod_econtent_binding().unwrap())],
                        "return[0]"
                    );

                    assert_eq!(
                        names[index_of(&public.sod_dsc_commitment().unwrap())],
                        "return[1]"
                    );

                    assert_eq!(
                        names[index_of(&public.sod_secret_binding().unwrap())],
                        "return[2]"
                    );
                }
                Circuit::DgExtract => {
                    assert_eq!(names[index_of(&public.dg_number().unwrap())], "dg_number");

                    assert_eq!(
                        names[index_of(&public.dg_extract_econtent_binding().unwrap())],
                        "econtent_binding"
                    );

                    assert_eq!(
                        names[index_of(&public.dg_extract_dg_binding().unwrap())],
                        "return[0]"
                    );
                }
                Circuit::Attributes => {
                    assert_eq!(
                        names[index_of(&public.attributes_dg_binding().unwrap())],
                        "dg_binding"
                    );

                    assert_eq!(
                        names[index_of(&public.attributes_current_date().unwrap())],
                        "current_yyyymmdd"
                    );

                    assert_eq!(
                        names[index_of(&public.attributes_commitment().unwrap())],
                        "return[0]"
                    );
                }
                Circuit::Compare | Circuit::Member | Circuit::Reveal => {
                    assert_eq!(names[index_of(&public.field_id().unwrap())], "field_id");

                    assert_eq!(
                        names[index_of(&public.referenced_commitment().unwrap())],
                        "commitment"
                    );
                }
                Circuit::AnchorInclusion => {
                    assert_eq!(
                        names[index_of(&public.anchor_registry_root().unwrap())],
                        "registry_root"
                    );

                    assert_eq!(
                        names[index_of(&public.anchor_dsc_commitment().unwrap())],
                        "return[0]"
                    );
                }
                Circuit::AnchorChain => {
                    assert_eq!(
                        names[index_of(&public.anchor_registry_root().unwrap())],
                        "master_list_root"
                    );

                    assert_eq!(
                        names[index_of(&public.anchor_current_date().unwrap())],
                        "current_yyyymmdd"
                    );

                    assert_eq!(
                        names[index_of(&public.anchor_dsc_commitment().unwrap())],
                        "return[0]"
                    );
                }
                Circuit::Nullifier => {
                    assert_eq!(
                        names[index_of(&public.referenced_commitment().unwrap())],
                        "commitment"
                    );

                    assert_eq!(
                        names[index_of(&public.nullifier_secret_binding().unwrap())],
                        "secret_binding"
                    );

                    assert_eq!(
                        names[index_of(&public.nullifier_value().unwrap())],
                        "return[0]"
                    );
                }
            }
        }
    }
}
