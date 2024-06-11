"use strict";(self.webpackChunkdocusaurus=self.webpackChunkdocusaurus||[]).push([[2763],{2784:(e,t,i)=>{i.r(t),i.d(t,{assets:()=>o,contentTitle:()=>l,default:()=>d,frontMatter:()=>s,metadata:()=>a,toc:()=>u});var n=i(4848),r=i(8453);const s={sidebar_position:25},l="ADR 4: Deferred unlifting in Plutus Core",a={id:"adr/adr4",title:"ADR 4: Deferred unlifting in Plutus Core",description:"Date: 2022-11",source:"@site/docs/adr/adr4.md",sourceDirName:"adr",slug:"/adr/adr4",permalink:"/plutus/master/docs/adr/adr4",draft:!1,unlisted:!1,editUrl:"https://github.com/IntersectMBO/plutus/edit/master/docusaurus/docs/adr/adr4.md",tags:[],version:"current",sidebarPosition:25,frontMatter:{sidebar_position:25},sidebar:"tutorialSidebar",previous:{title:"ADR 3: Sharing code between the production and debugging CEK machine",permalink:"/plutus/master/docs/adr/adr3"},next:{title:"Reference",permalink:"/plutus/master/docs/category/reference"}},o={},u=[{value:"Authors",id:"authors",level:2},{value:"Status",id:"status",level:2},{value:"Context",id:"context",level:2},{value:"Decision",id:"decision",level:2},{value:"Argument",id:"argument",level:2},{value:"Alternatives",id:"alternatives",level:2},{value:"1. Status quo",id:"1-status-quo",level:3},{value:"2. Support both versions forever",id:"2-support-both-versions-forever",level:3},{value:"Implications",id:"implications",level:2},{value:"Notes",id:"notes",level:2}];function h(e){const t={a:"a",code:"code",em:"em",h1:"h1",h2:"h2",h3:"h3",li:"li",p:"p",pre:"pre",ul:"ul",...(0,r.R)(),...e.components};return(0,n.jsxs)(n.Fragment,{children:[(0,n.jsx)(t.h1,{id:"adr-4-deferred-unlifting-in-plutus-core",children:"ADR 4: Deferred unlifting in Plutus Core"}),"\n",(0,n.jsx)(t.p,{children:"Date: 2022-11"}),"\n",(0,n.jsx)(t.h2,{id:"authors",children:"Authors"}),"\n",(0,n.jsx)(t.p,{children:(0,n.jsx)(t.a,{href:"mailto:michael.peyton-jones@iohk.io",children:"Michael Peyton Jones"})}),"\n",(0,n.jsx)(t.h2,{id:"status",children:"Status"}),"\n",(0,n.jsx)(t.p,{children:"Accepted"}),"\n",(0,n.jsx)(t.h2,{id:"context",children:"Context"}),"\n",(0,n.jsx)(t.p,{children:'A key part of the evaluation of builtin applications in Plutus Core is "unlifting".\nUnlifting is the process of taking a Plutus Core term and turning it into a Haskell value of a known type.\nFor example, we can unlift an integer constant term into the actual Haskell integer it contains.\nThis is necessary in order to apply the denotation of the builtin being applied, since that is a Haskell function that operates on Haskell types (e.g. integer addition).'}),"\n",(0,n.jsxs)(t.p,{children:["However, unlifting can fail: we cannot unlift a ",(0,n.jsx)(t.em,{children:"string"})," constant into a Haskell integer.\nThis failure is visible in program execution, since it terminates the program with an error."]}),"\n",(0,n.jsx)(t.p,{children:"The original design of the builtin application machinery performed unlifting of an argument as soon as it was received.\nThis meant that unlifting failures would surface at that point, whereas most of the errors that relate to builtin evaluation can only occur once the builtin has all its arguments, since that's when we run the actual function."}),"\n",(0,n.jsx)(t.p,{children:"For example:"}),"\n",(0,n.jsx)(t.pre,{children:(0,n.jsx)(t.code,{children:'[(builtin addInteger) (con string "hello")]\n'})}),"\n",(0,n.jsxs)(t.p,{children:["would fail (due to the unlifting failure), even though the builtin ",(0,n.jsx)(t.em,{children:"never"})," receives all its arguments and is never fully evaluated."]}),"\n",(0,n.jsx)(t.p,{children:'The fact that unlifting errors occur early on makes the specification of the behaviour of builtins significantly more complex.\nIt would be simpler if unlifting errors occurred when the builtin has all its arguments.\nWe refer to these two alternatives as "immediate" unlifting (the status quo) and "deferred" unlifting.'}),"\n",(0,n.jsx)(t.p,{children:"Deferred unlifting only makes evaluation slightly more lenient: some terms (such as the above example) do not give an error where they would do with immediate unlifting."}),"\n",(0,n.jsx)(t.h2,{id:"decision",children:"Decision"}),"\n",(0,n.jsx)(t.p,{children:"We decided:"}),"\n",(0,n.jsxs)(t.ul,{children:["\n",(0,n.jsx)(t.li,{children:"To switch to deferred unlifting by default in protocol version 7 (Vasil)."}),"\n",(0,n.jsx)(t.li,{children:"Having observed (after the hard fork) that no script evaluation in the history of the chain relied on immediate unlifting, to remove all support for immediate unlifting from the evaluator."}),"\n"]}),"\n",(0,n.jsx)(t.h2,{id:"argument",children:"Argument"}),"\n",(0,n.jsxs)(t.p,{children:["The difference between immediate and deferred unlifting is only visible in quite specific circumstances.\nSince builtins are ",(0,n.jsx)(t.em,{children:"usually"})," fully applied (otherwise they don't do anything), an unlifting error will usually be forced right away, regardless of whether we use immediate or deferred unlifting.\nThe only case where this is not true is where the builtin ",(0,n.jsx)(t.em,{children:"never"})," receives all its arguments, such as the example given above.\nMore generally, the only case where behaviour differs is ",(0,n.jsx)(t.em,{children:"partially applied"})," builtins which are applied to ",(0,n.jsx)(t.em,{children:"ill-typed arguments"}),".\nThis is quite unusual, since users typically write programs that a) do something and b) are well-typed."]}),"\n",(0,n.jsx)(t.p,{children:"Consequently, we felt that it was safe to change the default unlifting behaviour."}),"\n",(0,n.jsxs)(t.p,{children:["However, in order to gain the full benefit of simplification, we would like to remove the existence of immediate unlifting entirely.\nIf historical script evaluations on the chain still rely on immediate unlifting, then we must support it (and specify it) forever.\nHowever, once the default has changed, if the history of the chain still validates with ",(0,n.jsx)(t.em,{children:"deferred"})," unlifting, then we know that no historical script evaluations relied on that behaviour.\nAt that point we can ",(0,n.jsx)(t.em,{children:"unconditionally"})," enable deferred unlifting without worrying about not being able to validate the chain."]}),"\n",(0,n.jsx)(t.p,{children:"In theory, there could be outputs locked with script hashes whose behaviour would (if they are ever spent) rely on inmmediate unlifting.\nWe cannot rule this out, but given that it has never been relevant in the entire history of the chain, we considered this to be extremely unlikely."}),"\n",(0,n.jsx)(t.h2,{id:"alternatives",children:"Alternatives"}),"\n",(0,n.jsx)(t.h3,{id:"1-status-quo",children:"1. Status quo"}),"\n",(0,n.jsx)(t.p,{children:"Undesirable, we face the complexity forever."}),"\n",(0,n.jsx)(t.h3,{id:"2-support-both-versions-forever",children:"2. Support both versions forever"}),"\n",(0,n.jsx)(t.p,{children:"Arguably even worse than 1, in that we have to maintain and specify both versions forever, so our complexity burden is even greater."}),"\n",(0,n.jsx)(t.h2,{id:"implications",children:"Implications"}),"\n",(0,n.jsx)(t.p,{children:"This has already been implemented, and the specification has been updated.\nIt has no further implications for other decisions that we know of."}),"\n",(0,n.jsx)(t.h2,{id:"notes",children:"Notes"}),"\n",(0,n.jsx)(t.p,{children:"Relevant PRs:"}),"\n",(0,n.jsxs)(t.ul,{children:["\n",(0,n.jsx)(t.li,{children:(0,n.jsx)(t.a,{href:"https://github.com/IntersectMBO/plutus/pull/4516",children:"Support for both versions of unlifting"})}),"\n",(0,n.jsx)(t.li,{children:(0,n.jsx)(t.a,{href:"https://github.com/IntersectMBO/plutus/pull/4522",children:"Choose the unlifting mode based on protocol version"})}),"\n",(0,n.jsx)(t.li,{children:(0,n.jsx)(t.a,{href:"https://github.com/IntersectMBO/plutus/pull/4879",children:"Remove immediate unlifting"})}),"\n",(0,n.jsx)(t.li,{children:(0,n.jsx)(t.a,{href:"https://github.com/IntersectMBO/plutus/pull/4726",children:"Mainnet script dump test"})}),"\n",(0,n.jsx)(t.li,{children:(0,n.jsx)(t.a,{href:"https://github.com/IntersectMBO/plutus/pull/4960",children:"Update PLC specification for deferred unlifting"})}),"\n"]})]})}function d(e={}){const{wrapper:t}={...(0,r.R)(),...e.components};return t?(0,n.jsx)(t,{...e,children:(0,n.jsx)(h,{...e})}):h(e)}},8453:(e,t,i)=>{i.d(t,{R:()=>l,x:()=>a});var n=i(6540);const r={},s=n.createContext(r);function l(e){const t=n.useContext(s);return n.useMemo((function(){return"function"==typeof e?e(t):{...t,...e}}),[t,e])}function a(e){let t;return t=e.disableParentContext?"function"==typeof e.components?e.components(r):e.components||r:l(e.components),n.createElement(s.Provider,{value:t},e.children)}}}]);