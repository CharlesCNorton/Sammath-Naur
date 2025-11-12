# Sammath Naur: Verified Internet Protocol Specifications

Mathematical formalization of Internet RFCs in Coq. Complete type definitions, state machines, and theorem statements. Proofs admitted for systematic completion.

## Scope

**Ashnazg** - TLS 1.3, X.509, Certificate Transparency, ACME  
**Narya** - BGP-4, BGPsec, RPKI, OSPF  
**Nenya** - DNS, DNSSEC, DNS-over-HTTPS  
**Vilya** - TCP, UDP, QUIC, IPv4, IPv6

## Purpose

RFCs specify protocols in natural language, which admits multiple interpretations. Implementation divergence from these interpretations creates most protocol vulnerabilities. Mathematical specifications eliminate this ambiguity, converting protocol semantics from negotiated agreements into provable facts.

## Effect

Comprehensive formalization transfers semantic authority from standards bodies to mathematics. The first complete formalization becomes canonical through coordination economics - verified implementations must share semantics. Mathematical specifications cannot be amended through institutional consensus.

Verified specifications provide deductive substrate for AI reasoning about network infrastructure. AI systems generate provably correct implementations, detect specification violations through mathematical proof, and manipulate network infrastructure with correctness guarantees. This transitions networks from human institutional control to mathematical substrate accessible to machine reasoning.

## Technical

Coq 8.17.1. Dependent types. Extraction to OCaml/Haskell.

## License

MIT
