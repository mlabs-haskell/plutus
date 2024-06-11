"use strict";(self.webpackChunkdocusaurus=self.webpackChunkdocusaurus||[]).push([[105],{9432:(e,n,i)=>{i.r(n),i.d(n,{assets:()=>o,contentTitle:()=>a,default:()=>u,frontMatter:()=>r,metadata:()=>l,toc:()=>c});var s=i(4848),t=i(8453);const r={sidebar_position:25},a="Plutus language changes",l={id:"reference/plutus-language-changes",title:"Plutus language changes",description:"Language versions",source:"@site/docs/reference/plutus-language-changes.md",sourceDirName:"reference",slug:"/reference/plutus-language-changes",permalink:"/plutus/master/docs/reference/plutus-language-changes",draft:!1,unlisted:!1,editUrl:"https://github.com/IntersectMBO/plutus/edit/master/docusaurus/docs/reference/plutus-language-changes.md",tags:[],version:"current",sidebarPosition:25,frontMatter:{sidebar_position:25},sidebar:"tutorialSidebar",previous:{title:"Common weaknesses",permalink:"/plutus/master/docs/reference/common-weaknesses"},next:{title:"Upgrading to Vasil and Plutus script addresses",permalink:"/plutus/master/docs/reference/upgrade-vasil-plutus-script-addresses"}},o={},c=[{value:"Language versions",id:"language-versions",level:2},{value:"Plutus V1",id:"plutus-v1",level:3},{value:"Plutus V2",id:"plutus-v2",level:3},{value:"Examples",id:"examples",level:2},{value:"Built-in functions and types",id:"built-in-functions-and-types",level:2},{value:"Alonzo",id:"alonzo",level:3},{value:"Vasil",id:"vasil",level:3},{value:"PlutusV3",id:"plutusv3",level:3},{value:"Sums of products",id:"sums-of-products",level:3},{value:"New cryptographic primitives",id:"new-cryptographic-primitives",level:3},{value:"Bitwise primitives",id:"bitwise-primitives",level:3}];function d(e){const n={a:"a",code:"code",h1:"h1",h2:"h2",h3:"h3",li:"li",p:"p",strong:"strong",ul:"ul",...(0,t.R)(),...e.components};return(0,s.jsxs)(s.Fragment,{children:[(0,s.jsx)(n.h1,{id:"plutus-language-changes",children:"Plutus language changes"}),"\n",(0,s.jsx)(n.h2,{id:"language-versions",children:"Language versions"}),"\n",(0,s.jsxs)(n.p,{children:["See the documentation on ",(0,s.jsx)(n.code,{children:"language versions <what_are_plutus_language_versions>"})," for an explanation of what they are."]}),"\n",(0,s.jsx)(n.h3,{id:"plutus-v1",children:"Plutus V1"}),"\n",(0,s.jsxs)(n.p,{children:[(0,s.jsx)(n.code,{children:"PlutusV1"})," was the initial version of Plutus, introduced in the Alonzo hard fork."]}),"\n",(0,s.jsx)(n.h3,{id:"plutus-v2",children:"Plutus V2"}),"\n",(0,s.jsxs)(n.p,{children:[(0,s.jsx)(n.code,{children:"PlutusV2"})," was introduced in the Vasil hard fork."]}),"\n",(0,s.jsxs)(n.p,{children:["The main changes in ",(0,s.jsx)(n.code,{children:"PlutusV2"})," were to the interface to scripts.\nThe ",(0,s.jsx)(n.code,{children:"ScriptContext"})," was extended to include the following information:"]}),"\n",(0,s.jsxs)(n.ul,{children:["\n",(0,s.jsx)(n.li,{children:'The full "redeemers" structure, which contains all the redeemers used in the transaction'}),"\n",(0,s.jsxs)(n.li,{children:["Reference inputs in the transaction (proposed in ",(0,s.jsx)(n.a,{href:"https://cips.cardano.org/cips/cip31/",children:"CIP-31"}),")"]}),"\n",(0,s.jsxs)(n.li,{children:["Inline datums in the transaction (proposed in ",(0,s.jsx)(n.a,{href:"https://cips.cardano.org/cips/cip32/",children:"CIP-32"}),")"]}),"\n",(0,s.jsxs)(n.li,{children:["Reference scripts in the transaction (proposed in ",(0,s.jsx)(n.a,{href:"https://cips.cardano.org/cips/cip33/",children:"CIP-33"}),")"]}),"\n"]}),"\n",(0,s.jsx)(n.h2,{id:"examples",children:"Examples"}),"\n",(0,s.jsxs)(n.ul,{children:["\n",(0,s.jsx)(n.li,{children:(0,s.jsx)(n.a,{href:"https://github.com/IntersectMBO/cardano-node/blob/master/doc/reference/plutus/babbage-script-example.md",children:"Plutus V2 functionalities"})}),"\n",(0,s.jsx)(n.li,{children:(0,s.jsx)(n.a,{href:"https://github.com/perturbing/vasil-tests/blob/main/reference-inputs-cip-31.md",children:"How to use reference inputs"})}),"\n",(0,s.jsx)(n.li,{children:(0,s.jsx)(n.a,{href:"https://github.com/perturbing/vasil-tests/blob/main/inline-datums-cip-32.md",children:"How to use inline datums"})}),"\n",(0,s.jsx)(n.li,{children:(0,s.jsx)(n.a,{href:"https://github.com/perturbing/vasil-tests/blob/main/referencing-scripts-cip-33.md",children:"How to reference scripts"})}),"\n",(0,s.jsx)(n.li,{children:(0,s.jsx)(n.a,{href:"https://github.com/perturbing/vasil-tests/blob/main/collateral-output-cip-40.md",children:"How to use collateral outputs"})}),"\n"]}),"\n",(0,s.jsx)(n.h2,{id:"built-in-functions-and-types",children:"Built-in functions and types"}),"\n",(0,s.jsx)(n.p,{children:"Built-in functions and types can be introduced with just a hard fork.\nIn some cases they are also available only in particular language versions.\nThis section indicates in which hard fork particular built-ins were introduced, and any language version constraints."}),"\n",(0,s.jsx)(n.h3,{id:"alonzo",children:"Alonzo"}),"\n",(0,s.jsxs)(n.p,{children:["This is when the majority of the built-in types and functions were added to ",(0,s.jsx)(n.code,{children:"PlutusV1"}),".\nYou can find an enumeration of them in ",(0,s.jsx)(n.strong,{children:"add cross-reference link"})," : [plutus-core-spec]."]}),"\n",(0,s.jsx)(n.h3,{id:"vasil",children:"Vasil"}),"\n",(0,s.jsxs)(n.p,{children:["All of the built-in types and functions from ",(0,s.jsx)(n.code,{children:"PlutusV1"})," were added to ",(0,s.jsx)(n.code,{children:"PlutusV2"}),"."]}),"\n",(0,s.jsxs)(n.p,{children:["The following built-in function was added to ",(0,s.jsx)(n.code,{children:"PlutusV2"})," only (i.e., it is not available in ",(0,s.jsx)(n.code,{children:"PlutusV1"}),")."]}),"\n",(0,s.jsxs)(n.ul,{children:["\n",(0,s.jsxs)(n.li,{children:[(0,s.jsx)(n.code,{children:"serializeData"})," (proposed in ",(0,s.jsx)(n.a,{href:"https://cips.cardano.org/cips/cip42/",children:"CIP-42"}),")"]}),"\n"]}),"\n",(0,s.jsx)(n.h3,{id:"plutusv3",children:"PlutusV3"}),"\n",(0,s.jsxs)(n.p,{children:["Plutus and cryptography teams at IOG, in collaboration with ",(0,s.jsx)(n.a,{href:"https://mlabs.city/",children:"MLabs"}),", continue to develop Plutus capabilities.\nStarting with the release of ",(0,s.jsx)(n.a,{href:"https://github.com/IntersectMBO/cardano-node/releases/tag/8.8.0-pre",children:"Cardano node v.8.8.0-pre"}),", ",(0,s.jsx)(n.code,{children:"PlutusV3"})," is available on ",(0,s.jsx)(n.a,{href:"https://sancho.network/",children:"SanchoNet"}),", introducing the Cardano community to governance features from ",(0,s.jsx)(n.a,{href:"https://cips.cardano.org/cip/CIP-1694#goal",children:"CIP-1694"})," in a controlled testnet environment."]}),"\n",(0,s.jsxs)(n.p,{children:[(0,s.jsx)(n.code,{children:"PlutusV3"})," is the new ledger language that enhances Plutus Core's cryptographic capabilities, offering the following benefits for the smart contract developer community:"]}),"\n",(0,s.jsxs)(n.ul,{children:["\n",(0,s.jsxs)(n.li,{children:["Providing an updated script context that will let users see ",(0,s.jsx)(n.a,{href:"https://cips.cardano.org/cip/CIP-1694#goal",children:"CIP-1694"})," governance-related entities and voting features"]}),"\n",(0,s.jsx)(n.li,{children:"Interoperability between blockchains"}),"\n",(0,s.jsx)(n.li,{children:"Advanced Plutus primitives"}),"\n",(0,s.jsx)(n.li,{children:"Well-known and optimal cryptographic algorithms"}),"\n",(0,s.jsx)(n.li,{children:"Support for porting of smart contracts from Ethereum"}),"\n",(0,s.jsx)(n.li,{children:"Creating sidechain bridges"}),"\n",(0,s.jsx)(n.li,{children:"Improving performance by adding a sums of products (SOPs) feature to support the direct encoding of differrent data types."}),"\n"]}),"\n",(0,s.jsx)(n.h3,{id:"sums-of-products",children:"Sums of products"}),"\n",(0,s.jsxs)(n.p,{children:[(0,s.jsx)(n.code,{children:"PlutusV3"})," introduces sums of products - a way of encoding data types that leads to smaller and cheaper scripts compared with ",(0,s.jsx)(n.a,{href:"https://en.wikipedia.org/wiki/Mogensen%E2%80%93Scott_encoding",children:"Scott encoding"}),", a common way of encoding data types in Plutus Core."]}),"\n",(0,s.jsxs)(n.p,{children:["The sums of products approach aims to boost script efficiency and improve code generation for Plutus Core compilers.\nThe changes involve new term constructors for packing fields into constructor values and efficient tag inspection for case branches, potentially running programs 30% faster.\nFor an in-depth discussion, see ",(0,s.jsx)(n.a,{href:"https://cips.cardano.org/cip/CIP-0085",children:"CIP-85"}),"."]}),"\n",(0,s.jsx)(n.h3,{id:"new-cryptographic-primitives",children:"New cryptographic primitives"}),"\n",(0,s.jsxs)(n.p,{children:[(0,s.jsx)(n.code,{children:"PlutusV3"})," provides new built-in primitives that expand the language's capabilities."]}),"\n",(0,s.jsxs)(n.ul,{children:["\n",(0,s.jsxs)(n.li,{children:[(0,s.jsx)(n.strong,{children:"BLS12-381"}),": A curve pairing that includes 17 primitives that support cryptographic curves. This is a benefit to sidechain specification implementation and ",(0,s.jsx)(n.a,{href:"https://iohk.io/en/blog/posts/2023/07/20/mithril-nears-mainnet-release/",children:"Mithril"})," integration."]}),"\n",(0,s.jsxs)(n.li,{children:[(0,s.jsx)(n.strong,{children:"Blake2b-224"}),": A cryptographic hash function for on-chain computation of public-key hashes for the validation of transaction signatures. Supports community projects and contributes to Cardano's versatility."]}),"\n",(0,s.jsxs)(n.li,{children:[(0,s.jsx)(n.strong,{children:"Keccak-256"}),": A cryptographic hash function that produces a 256-bit (32-byte) hash value, commonly used for secure data verification. Supports Ethereum signature verification within scripts and cross-chain solutions."]}),"\n"]}),"\n",(0,s.jsx)(n.h3,{id:"bitwise-primitives",children:"Bitwise primitives"}),"\n",(0,s.jsxs)(n.p,{children:["PlutusV3 initially brings several new bitwise primitives (with more to come at later stages).\nThe introduction of ",(0,s.jsx)(n.a,{href:"https://cips.cardano.org/cip/CIP-0058",children:"CIP-58"})," bitwise primitives will enable the following features:"]}),"\n",(0,s.jsxs)(n.ul,{children:["\n",(0,s.jsx)(n.li,{children:"Very low-level bit manipulations within Plutus, supporting the ability to execute high-performance data manipulation operations."}),"\n",(0,s.jsx)(n.li,{children:"Supporting the implementation of secure and robust cryptographic algorithms within Plutus."}),"\n",(0,s.jsx)(n.li,{children:"Facilitating standard, high-performance implementations for conversions between integers and bytestrings."}),"\n"]}),"\n",(0,s.jsxs)(n.p,{children:[(0,s.jsx)(n.code,{children:"PlutusV3"})," adds two bitwise primitives: ",(0,s.jsx)(n.code,{children:"integerToByteString"})," and ",(0,s.jsx)(n.code,{children:"byteStringToInteger"}),".\nThe remaining primitives will be added to ",(0,s.jsx)(n.code,{children:"PlutusV3"})," gradually and will not require a new ledger language."]})]})}function u(e={}){const{wrapper:n}={...(0,t.R)(),...e.components};return n?(0,s.jsx)(n,{...e,children:(0,s.jsx)(d,{...e})}):d(e)}},8453:(e,n,i)=>{i.d(n,{R:()=>a,x:()=>l});var s=i(6540);const t={},r=s.createContext(t);function a(e){const n=s.useContext(r);return s.useMemo((function(){return"function"==typeof e?e(n):{...n,...e}}),[n,e])}function l(e){let n;return n=e.disableParentContext?"function"==typeof e.components?e.components(t):e.components||t:a(e.components),s.createElement(r.Provider,{value:n},e.children)}}}]);