"use strict";(self.webpackChunkdocusaurus=self.webpackChunkdocusaurus||[]).push([[1929],{8101:(e,t,s)=>{s.r(t),s.d(t,{assets:()=>l,contentTitle:()=>d,default:()=>a,frontMatter:()=>n,metadata:()=>c,toc:()=>o});var i=s(4848),r=s(8453);const n={sidebar_position:5},d="Plutus Tx compiler options",c={id:"reference/plutus-tx-compiler-options",title:"Plutus Tx compiler options",description:"These options can be passed to the compiler via the OPTIONS_GHC pragma, for instance",source:"@site/docs/reference/plutus-tx-compiler-options.md",sourceDirName:"reference",slug:"/reference/plutus-tx-compiler-options",permalink:"/plutus/master/docs/reference/plutus-tx-compiler-options",draft:!1,unlisted:!1,editUrl:"https://github.com/IntersectMBO/plutus/edit/master/docusaurus/docs/reference/plutus-tx-compiler-options.md",tags:[],version:"current",sidebarPosition:5,frontMatter:{sidebar_position:5},sidebar:"tutorialSidebar",previous:{title:"Reference",permalink:"/plutus/master/docs/category/reference"},next:{title:"Optimization techniques for Plutus scripts",permalink:"/plutus/master/docs/reference/script-optimization-techniques"}},l={},o=[];function h(e){const t={code:"code",h1:"h1",p:"p",pre:"pre",table:"table",tbody:"tbody",td:"td",th:"th",thead:"thead",tr:"tr",...(0,r.R)(),...e.components};return(0,i.jsxs)(i.Fragment,{children:[(0,i.jsx)(t.h1,{id:"plutus-tx-compiler-options",children:"Plutus Tx compiler options"}),"\n",(0,i.jsxs)(t.p,{children:["These options can be passed to the compiler via the ",(0,i.jsx)(t.code,{children:"OPTIONS_GHC"})," pragma, for instance"]}),"\n",(0,i.jsx)(t.pre,{children:(0,i.jsx)(t.code,{className:"language-haskell",children:"{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:dump-uplc #-}\n{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations=3 #-}\n"})}),"\n",(0,i.jsxs)(t.p,{children:["For each boolean option, you can add a ",(0,i.jsx)(t.code,{children:"no-"})," prefix to switch it off, such as ",(0,i.jsx)(t.code,{children:"no-typecheck"}),", ",(0,i.jsx)(t.code,{children:"no-simplifier-beta"}),"."]}),"\n",(0,i.jsxs)(t.table,{children:[(0,i.jsx)(t.thead,{children:(0,i.jsxs)(t.tr,{children:[(0,i.jsx)(t.th,{children:"Option"}),(0,i.jsx)(t.th,{children:"Value Type"}),(0,i.jsx)(t.th,{children:"Default"}),(0,i.jsx)(t.th,{children:"Description"})]})}),(0,i.jsxs)(t.tbody,{children:[(0,i.jsxs)(t.tr,{children:[(0,i.jsx)(t.td,{children:(0,i.jsx)(t.code,{children:"conservative-optimisation"})}),(0,i.jsx)(t.td,{children:"Bool"}),(0,i.jsx)(t.td,{children:"False"}),(0,i.jsxs)(t.td,{children:["When conservative optimisation is used, only the optimisations that never make the program worse (in terms of cost or size) are employed. Implies ",(0,i.jsx)(t.code,{children:"no-relaxed-float-in"}),"."]})]}),(0,i.jsxs)(t.tr,{children:[(0,i.jsx)(t.td,{children:(0,i.jsx)(t.code,{children:"context-level"})}),(0,i.jsx)(t.td,{children:"Int"}),(0,i.jsx)(t.td,{children:"1"}),(0,i.jsx)(t.td,{children:"Set context level for error messages."})]}),(0,i.jsxs)(t.tr,{children:[(0,i.jsx)(t.td,{children:(0,i.jsx)(t.code,{children:"coverage-all"})}),(0,i.jsx)(t.td,{children:"Bool"}),(0,i.jsx)(t.td,{children:"False"}),(0,i.jsx)(t.td,{children:"Add all available coverage annotations in the trace output"})]}),(0,i.jsxs)(t.tr,{children:[(0,i.jsx)(t.td,{children:(0,i.jsx)(t.code,{children:"coverage-boolean"})}),(0,i.jsx)(t.td,{children:"Bool"}),(0,i.jsx)(t.td,{children:"False"}),(0,i.jsx)(t.td,{children:"Add boolean coverage annotations in the trace output"})]}),(0,i.jsxs)(t.tr,{children:[(0,i.jsx)(t.td,{children:(0,i.jsx)(t.code,{children:"coverage-location"})}),(0,i.jsx)(t.td,{children:"Bool"}),(0,i.jsx)(t.td,{children:"False"}),(0,i.jsx)(t.td,{children:"Add location coverage annotations in the trace output"})]}),(0,i.jsxs)(t.tr,{children:[(0,i.jsx)(t.td,{children:(0,i.jsx)(t.code,{children:"defer-errors"})}),(0,i.jsx)(t.td,{children:"Bool"}),(0,i.jsx)(t.td,{children:"False"}),(0,i.jsx)(t.td,{children:"If a compilation error happens and this option is turned on, the compilation error is suppressed and the original Haskell expression is replaced with a runtime-error expression."})]}),(0,i.jsxs)(t.tr,{children:[(0,i.jsx)(t.td,{children:(0,i.jsx)(t.code,{children:"dump-compilation-trace"})}),(0,i.jsx)(t.td,{children:"Bool"}),(0,i.jsx)(t.td,{children:"False"}),(0,i.jsx)(t.td,{children:"Dump compilation trace for debugging"})]}),(0,i.jsxs)(t.tr,{children:[(0,i.jsx)(t.td,{children:(0,i.jsx)(t.code,{children:"dump-pir"})}),(0,i.jsx)(t.td,{children:"Bool"}),(0,i.jsx)(t.td,{children:"False"}),(0,i.jsx)(t.td,{children:"Dump Plutus IR"})]}),(0,i.jsxs)(t.tr,{children:[(0,i.jsx)(t.td,{children:(0,i.jsx)(t.code,{children:"dump-plc"})}),(0,i.jsx)(t.td,{children:"Bool"}),(0,i.jsx)(t.td,{children:"False"}),(0,i.jsx)(t.td,{children:"Dump Typed Plutus Core"})]}),(0,i.jsxs)(t.tr,{children:[(0,i.jsx)(t.td,{children:(0,i.jsx)(t.code,{children:"dump-uplc"})}),(0,i.jsx)(t.td,{children:"Bool"}),(0,i.jsx)(t.td,{children:"False"}),(0,i.jsx)(t.td,{children:"Dump Untyped Plutus Core"})]}),(0,i.jsxs)(t.tr,{children:[(0,i.jsx)(t.td,{children:(0,i.jsx)(t.code,{children:"max-cse-iterations"})}),(0,i.jsx)(t.td,{children:"Int"}),(0,i.jsx)(t.td,{children:"4"}),(0,i.jsx)(t.td,{children:"Set the max iterations for CSE"})]}),(0,i.jsxs)(t.tr,{children:[(0,i.jsx)(t.td,{children:(0,i.jsx)(t.code,{children:"max-simplifier-iterations-pir"})}),(0,i.jsx)(t.td,{children:"Int"}),(0,i.jsx)(t.td,{children:"12"}),(0,i.jsx)(t.td,{children:"Set the max iterations for the PIR simplifier"})]}),(0,i.jsxs)(t.tr,{children:[(0,i.jsx)(t.td,{children:(0,i.jsx)(t.code,{children:"max-simplifier-iterations-uplc"})}),(0,i.jsx)(t.td,{children:"Int"}),(0,i.jsx)(t.td,{children:"12"}),(0,i.jsx)(t.td,{children:"Set the max iterations for the UPLC simplifier"})]}),(0,i.jsxs)(t.tr,{children:[(0,i.jsx)(t.td,{children:(0,i.jsx)(t.code,{children:"optimize"})}),(0,i.jsx)(t.td,{children:"Bool"}),(0,i.jsx)(t.td,{children:"True"}),(0,i.jsx)(t.td,{children:"Run optimization passes such as simplification and floating let-bindings."})]}),(0,i.jsxs)(t.tr,{children:[(0,i.jsx)(t.td,{children:(0,i.jsx)(t.code,{children:"pedantic"})}),(0,i.jsx)(t.td,{children:"Bool"}),(0,i.jsx)(t.td,{children:"False"}),(0,i.jsx)(t.td,{children:"Run type checker after each compilation pass"})]}),(0,i.jsxs)(t.tr,{children:[(0,i.jsx)(t.td,{children:(0,i.jsx)(t.code,{children:"profile-all"})}),(0,i.jsx)(t.td,{children:"ProfileOpts"}),(0,i.jsx)(t.td,{children:"None"}),(0,i.jsx)(t.td,{children:"Set profiling options to All, which adds tracing when entering and exiting a term."})]}),(0,i.jsxs)(t.tr,{children:[(0,i.jsx)(t.td,{children:(0,i.jsx)(t.code,{children:"relaxed-float-in"})}),(0,i.jsx)(t.td,{children:"Bool"}),(0,i.jsx)(t.td,{children:"True"}),(0,i.jsx)(t.td,{children:"Use a more aggressive float-in pass, which often leads to reduced costs but may occasionally lead to slightly increased costs."})]}),(0,i.jsxs)(t.tr,{children:[(0,i.jsx)(t.td,{children:(0,i.jsx)(t.code,{children:"remove-trace"})}),(0,i.jsx)(t.td,{children:"Bool"}),(0,i.jsx)(t.td,{children:"False"}),(0,i.jsxs)(t.td,{children:["Eliminate calls to ",(0,i.jsx)(t.code,{children:"trace"})," from Plutus Core"]})]}),(0,i.jsxs)(t.tr,{children:[(0,i.jsx)(t.td,{children:(0,i.jsx)(t.code,{children:"simplifier-beta"})}),(0,i.jsx)(t.td,{children:"Bool"}),(0,i.jsx)(t.td,{children:"True"}),(0,i.jsx)(t.td,{children:"Run a simplification pass that performs beta transformations"})]}),(0,i.jsxs)(t.tr,{children:[(0,i.jsx)(t.td,{children:(0,i.jsx)(t.code,{children:"simplifier-inline"})}),(0,i.jsx)(t.td,{children:"Bool"}),(0,i.jsx)(t.td,{children:"True"}),(0,i.jsx)(t.td,{children:"Run a simplification pass that performs inlining"})]}),(0,i.jsxs)(t.tr,{children:[(0,i.jsx)(t.td,{children:(0,i.jsx)(t.code,{children:"simplifier-remove-dead-bindings"})}),(0,i.jsx)(t.td,{children:"Bool"}),(0,i.jsx)(t.td,{children:"True"}),(0,i.jsx)(t.td,{children:"Run a simplification pass that removes dead bindings"})]}),(0,i.jsxs)(t.tr,{children:[(0,i.jsx)(t.td,{children:(0,i.jsx)(t.code,{children:"simplifier-unwrap-cancel"})}),(0,i.jsx)(t.td,{children:"Bool"}),(0,i.jsx)(t.td,{children:"True"}),(0,i.jsx)(t.td,{children:"Run a simplification pass that cancels unwrap/wrap pairs"})]}),(0,i.jsxs)(t.tr,{children:[(0,i.jsx)(t.td,{children:(0,i.jsx)(t.code,{children:"strictify-bindings"})}),(0,i.jsx)(t.td,{children:"Bool"}),(0,i.jsx)(t.td,{children:"True"}),(0,i.jsx)(t.td,{children:"Run a simplification pass that makes bindings stricter"})]}),(0,i.jsxs)(t.tr,{children:[(0,i.jsx)(t.td,{children:(0,i.jsx)(t.code,{children:"target-version"})}),(0,i.jsx)(t.td,{children:"Version"}),(0,i.jsx)(t.td,{children:"1.1.0"}),(0,i.jsx)(t.td,{children:"The target Plutus Core language version"})]}),(0,i.jsxs)(t.tr,{children:[(0,i.jsx)(t.td,{children:(0,i.jsx)(t.code,{children:"typecheck"})}),(0,i.jsx)(t.td,{children:"Bool"}),(0,i.jsx)(t.td,{children:"True"}),(0,i.jsx)(t.td,{children:"Perform type checking during compilation."})]}),(0,i.jsxs)(t.tr,{children:[(0,i.jsx)(t.td,{children:(0,i.jsx)(t.code,{children:"verbosity"})}),(0,i.jsx)(t.td,{children:"Verbosity"}),(0,i.jsx)(t.td,{children:"Quiet"}),(0,i.jsx)(t.td,{children:"Set logging verbosity level (0=Quiet, 1=Verbose, 2=Debug)"})]})]})]})]})}function a(e={}){const{wrapper:t}={...(0,r.R)(),...e.components};return t?(0,i.jsx)(t,{...e,children:(0,i.jsx)(h,{...e})}):h(e)}},8453:(e,t,s)=>{s.d(t,{R:()=>d,x:()=>c});var i=s(6540);const r={},n=i.createContext(r);function d(e){const t=i.useContext(n);return i.useMemo((function(){return"function"==typeof e?e(t):{...t,...e}}),[t,e])}function c(e){let t;return t=e.disableParentContext?"function"==typeof e.components?e.components(r):e.components||r:d(e.components),i.createElement(n.Provider,{value:t},e.children)}}}]);