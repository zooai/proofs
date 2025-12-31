export type ProofTool = 'lean4' | 'halmos' | 'foundry'
export type ProofStatus = 'proved' | 'partial' | 'axiom'

export interface ProofConfig {
  id: string
  title: string
  subtitle: string
  abstract: string
  tool: ProofTool
  status: ProofStatus
  theoremCount: number
  sourceUrl: string
  githubUrl: string
  date: string
  authors: string[]
  tags: string[]
  relatedPapers?: string[]
}

export interface SiteConfig {
  name: string
  fullName: string
  description: string
  website: string
  github: string
  primaryColor: string
  secondaryColor: string
  accentColor: string
  logo: string
  proofs: ProofConfig[]
}

export const siteConfig: SiteConfig = {
  name: 'Zoo Labs',
  fullName: 'Zoo Labs Foundation',
  description: 'Machine-checked proofs for decentralized AI research, DeSci governance, and conservation protocols.',
  website: 'https://zoo.ngo',
  github: 'https://github.com/zooai',
  primaryColor: '#3498DB',
  secondaryColor: '#2980B9',
  accentColor: '#E67E22',
  logo: '/logos/zoo-logo.svg',
  proofs: [
    {
      id: 'poai-consensus',
      title: 'PoAI Consensus',
      subtitle: 'Proof of AI Consensus Correctness',
      abstract: 'Formal proof that the Proof of AI consensus mechanism satisfies safety and liveness under the assumed compute-attestation fault model. Includes quorum intersection for GPU-attested validators and finality guarantees.',
      tool: 'lean4',
      status: 'proved',
      theoremCount: 4,
      sourceUrl: 'https://github.com/zooai/proofs/blob/main/lean/Consensus/PoAI.lean',
      githubUrl: 'https://github.com/zooai/proofs',
      date: '2026-03-25',
      authors: ['Zach Kelling', 'Zoo Labs Research'],
      tags: ['PoAI', 'Consensus', 'GPU Attestation', 'Safety'],
      relatedPapers: ['PoAI Consensus Protocol'],
    },
    {
      id: 'dso-governance',
      title: 'DSO Governance',
      subtitle: 'Decentralized Science Organization Voting Safety',
      abstract: 'Formal verification of the DSO governance voting mechanism proving that no conflicting proposals can pass simultaneously, quorum thresholds are respected, and vote delegation preserves total weight.',
      tool: 'lean4',
      status: 'proved',
      theoremCount: 3,
      sourceUrl: 'https://github.com/zooai/proofs/blob/main/lean/Governance/DSO.lean',
      githubUrl: 'https://github.com/zooai/proofs',
      date: '2026-03-25',
      authors: ['Zach Kelling', 'Zoo Labs Research'],
      tags: ['DSO', 'Governance', 'Voting', 'DeSci'],
      relatedPapers: ['DSO Governance Framework'],
    },
    {
      id: 'experience-ledger',
      title: 'Experience Ledger',
      subtitle: 'On-Chain Experience Token Conservation',
      abstract: 'Proof that the experience token ledger satisfies conservation laws: total supply equals sum of all balances, minting is bounded by attestation events, and no experience can be created without verified contribution.',
      tool: 'halmos',
      status: 'proved',
      theoremCount: 3,
      sourceUrl: 'https://github.com/zooai/proofs/blob/main/halmos/ExperienceLedger.t.sol',
      githubUrl: 'https://github.com/zooai/proofs',
      date: '2026-03-25',
      authors: ['Zach Kelling', 'Zoo Labs Research'],
      tags: ['Experience', 'Conservation', 'Token', 'Symbolic'],
    },
    {
      id: 'federated-wildlife-ai',
      title: 'Federated Wildlife AI',
      subtitle: 'Federated Learning Convergence for Wildlife Models',
      abstract: 'Formal proof that the federated learning protocol for wildlife classification models converges under heterogeneous data distributions. Includes bounded gradient divergence and differential privacy guarantees.',
      tool: 'lean4',
      status: 'partial',
      theoremCount: 3,
      sourceUrl: 'https://github.com/zooai/proofs/blob/main/lean/AI/FederatedWildlife.lean',
      githubUrl: 'https://github.com/zooai/proofs',
      date: '2026-03-25',
      authors: ['Zach Kelling', 'Zoo Labs Research'],
      tags: ['Federated Learning', 'Wildlife', 'Convergence', 'Privacy'],
      relatedPapers: ['Federated Wildlife AI'],
    },
    {
      id: 'species-classification',
      title: 'Species Classification',
      subtitle: 'Model Accuracy Bounds',
      abstract: 'Machine-checked bounds on species classification model accuracy using certified robustness techniques. Proves that adversarial perturbations within epsilon-ball cannot change predictions beyond a quantified error rate.',
      tool: 'lean4',
      status: 'partial',
      theoremCount: 2,
      sourceUrl: 'https://github.com/zooai/proofs/blob/main/lean/AI/SpeciesClassification.lean',
      githubUrl: 'https://github.com/zooai/proofs',
      date: '2026-03-25',
      authors: ['Zach Kelling', 'Zoo Labs Research'],
      tags: ['Classification', 'Robustness', 'Accuracy', 'AI'],
      relatedPapers: ['Certified Species Classification'],
    },
    {
      id: 'conservation-impact-bonds',
      title: 'Conservation Impact Bonds',
      subtitle: 'Bond Pricing & Payout Correctness',
      abstract: 'Symbolic verification of conservation impact bond smart contracts proving that payout calculations are correct given oracle-attested outcomes, bond pricing respects no-arbitrage constraints, and early termination preserves principal.',
      tool: 'halmos',
      status: 'proved',
      theoremCount: 4,
      sourceUrl: 'https://github.com/zooai/proofs/blob/main/halmos/ConservationBonds.t.sol',
      githubUrl: 'https://github.com/zooai/proofs',
      date: '2026-03-25',
      authors: ['Zach Kelling', 'Zoo Labs Research'],
      tags: ['Bonds', 'Conservation', 'Pricing', 'Symbolic'],
    },
    {
      id: 'agent-nft-ownership',
      title: 'Agent NFT Ownership',
      subtitle: 'NFT-Bound Agent Permission Proofs',
      abstract: 'Formal proof that NFT-bound AI agent permissions satisfy access control lattice properties: ownership transfer correctly updates capability sets, delegation is transitive and revocable, and no agent can escalate beyond its grant.',
      tool: 'lean4',
      status: 'proved',
      theoremCount: 3,
      sourceUrl: 'https://github.com/zooai/proofs/blob/main/lean/Agents/NFTOwnership.lean',
      githubUrl: 'https://github.com/zooai/proofs',
      date: '2026-03-25',
      authors: ['Zach Kelling', 'Zoo Labs Research'],
      tags: ['NFT', 'Agents', 'Permissions', 'Access Control'],
    },
    {
      id: 'carbon-credit-verification',
      title: 'Carbon Credit Verification',
      subtitle: 'Credit Issuance Conservation Laws',
      abstract: 'Proof that the carbon credit issuance protocol satisfies strict conservation: credits cannot be double-counted, retirement is irreversible, and total issued credits are bounded by verified sequestration data from oracle attestations.',
      tool: 'halmos',
      status: 'proved',
      theoremCount: 3,
      sourceUrl: 'https://github.com/zooai/proofs/blob/main/halmos/CarbonCredit.t.sol',
      githubUrl: 'https://github.com/zooai/proofs',
      date: '2026-03-25',
      authors: ['Zach Kelling', 'Zoo Labs Research'],
      tags: ['Carbon', 'Credits', 'Conservation', 'Symbolic'],
    },
    {
      id: 'data-commons-access',
      title: 'Data Commons Access',
      subtitle: 'Access Control Lattice Proofs',
      abstract: 'Formal verification of the data commons access control system proving that the permission lattice forms a valid partial order, access grants are monotone, and revocation propagates correctly through the delegation graph.',
      tool: 'lean4',
      status: 'proved',
      theoremCount: 3,
      sourceUrl: 'https://github.com/zooai/proofs/blob/main/lean/DataCommons/Access.lean',
      githubUrl: 'https://github.com/zooai/proofs',
      date: '2026-03-25',
      authors: ['Zach Kelling', 'Zoo Labs Research'],
      tags: ['Data Commons', 'Access Control', 'Lattice', 'Permissions'],
      relatedPapers: ['Open Data Commons Protocol'],
    },
    {
      id: 'satellite-ecology',
      title: 'Satellite Ecology',
      subtitle: 'Remote Sensing Data Integrity',
      abstract: 'Proof that the satellite ecology data pipeline preserves integrity from capture to on-chain commitment. Includes Merkle proof verification for tiled imagery, timestamp monotonicity, and tamper-evidence for observation records.',
      tool: 'lean4',
      status: 'partial',
      theoremCount: 2,
      sourceUrl: 'https://github.com/zooai/proofs/blob/main/lean/Ecology/Satellite.lean',
      githubUrl: 'https://github.com/zooai/proofs',
      date: '2026-03-25',
      authors: ['Zach Kelling', 'Zoo Labs Research'],
      tags: ['Satellite', 'Ecology', 'Remote Sensing', 'Data Integrity'],
      relatedPapers: ['Satellite Ecology Protocol'],
    },
  ],
}
