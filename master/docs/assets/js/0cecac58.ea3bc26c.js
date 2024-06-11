"use strict";(self.webpackChunkdocusaurus=self.webpackChunkdocusaurus||[]).push([[9919],{5767:(e,t,i)=>{i.r(t),i.d(t,{assets:()=>c,contentTitle:()=>o,default:()=>p,frontMatter:()=>r,metadata:()=>a,toc:()=>l});var s=i(4848),n=i(8453);const r={sidebar_position:15},o="Exporting scripts, datums and redeemers",a={id:"working-with-scripts/exporting-scripts-datums-redeemers",title:"Exporting scripts, datums and redeemers",description:"NOTE",source:"@site/docs/working-with-scripts/exporting-scripts-datums-redeemers.md",sourceDirName:"working-with-scripts",slug:"/working-with-scripts/exporting-scripts-datums-redeemers",permalink:"/plutus/master/docs/working-with-scripts/exporting-scripts-datums-redeemers",draft:!1,unlisted:!1,editUrl:"https://github.com/IntersectMBO/plutus/edit/master/docusaurus/docs/working-with-scripts/exporting-scripts-datums-redeemers.md",tags:[],version:"current",sidebarPosition:15,frontMatter:{sidebar_position:15},sidebar:"tutorialSidebar",previous:{title:"Writing basic minting policies",permalink:"/plutus/master/docs/working-with-scripts/writing-basic-minting-policies"},next:{title:"Profiling the budget usage of Plutus scripts",permalink:"/plutus/master/docs/working-with-scripts/profiling-budget-usage"}},c={},l=[];function d(e){const t={a:"a",blockquote:"blockquote",code:"code",em:"em",h1:"h1",p:"p",pre:"pre",strong:"strong",...(0,n.R)(),...e.components},{LiteralInclude:i}=t;return i||function(e,t){throw new Error("Expected "+(t?"component":"object")+" `"+e+"` to be defined: you likely forgot to import, pass, or provide it.")}("LiteralInclude",!0),(0,s.jsxs)(s.Fragment,{children:[(0,s.jsx)(t.h1,{id:"exporting-scripts-datums-and-redeemers",children:"Exporting scripts, datums and redeemers"}),"\n",(0,s.jsxs)(t.blockquote,{children:["\n",(0,s.jsxs)(t.p,{children:["\ud83d\udccc"," ",(0,s.jsx)(t.strong,{children:"NOTE"})]}),"\n",(0,s.jsxs)(t.p,{children:["This guide uses the scripts from the topic ",(0,s.jsx)(t.a,{href:"/plutus/master/docs/working-with-scripts/writing-basic-validator-scripts",children:"Writing basic validator scripts"}),"."]}),"\n"]}),"\n",(0,s.jsx)(t.p,{children:"Since scripts must match their on-chain hashes exactly, it is important that the scripts which an application uses do not accidentally change.\nFor example, changing the source code or updating dependencies or tooling may lead to small changes in the script.\nAs a result, the hash will change.\nIn cases where the hashes must match exactly, even changes which do not alter the functionality of the script can be problematic."}),"\n",(0,s.jsxs)(t.p,{children:["For this reason, once you expect that you will not modify the on-chain part of your application more, it is sensible to ",(0,s.jsx)(t.em,{children:"freeze"})," it by saving the final Plutus Core to a file."]}),"\n",(0,s.jsx)(t.p,{children:"Additionally, while most Plutus Applications use scripts by directly submitting them as part of transactions from the application itself, it can be useful to be able to export a serialized script.\nFor example, you might want to submit it as part of a manually created transaction with the Cardano node CLI, or send it to another party for them to use."}),"\n",(0,s.jsxs)(t.p,{children:["Fortunately, it is quite simple to do this.\nMost of the types have typeclass instances for ",(0,s.jsx)(t.code,{children:"Serialise"})," which allows translating directly into CBOR.\nThis applies to ",(0,s.jsx)(t.code,{children:"Validator"}),", ",(0,s.jsx)(t.code,{children:"Redeemer"}),", and ",(0,s.jsx)(t.code,{children:"Datum"})," types.\nIf you want to create values that you can pass to the Cardano CLI, you will need to convert them to the appropriate types from ",(0,s.jsx)(t.code,{children:"cardano-api"})," and use ",(0,s.jsx)(t.code,{children:"serialiseToTextEnvelope"}),"."]}),"\n",(0,s.jsx)(i,{file:"BasicValidators.hs",language:"haskell",title:"Block Title",start:"-- BLOCK5",end:"-- BLOCK6"}),"\n",(0,s.jsxs)(t.p,{children:[(0,s.jsx)(t.code,{children:"CompiledCode"})," has a different serialization method, ",(0,s.jsx)(t.code,{children:"Flat"}),", but the principle is the same."]}),"\n",(0,s.jsxs)(t.p,{children:["The serialized form of ",(0,s.jsx)(t.code,{children:"CompiledCode"})," can also be dumped using a plugin option:"]}),"\n",(0,s.jsx)(t.pre,{children:(0,s.jsx)(t.code,{className:"language-haskell",children:"{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:dump-uplc #-}\n"})}),"\n",(0,s.jsx)(t.p,{children:"This will dump the output to a temporary file with a name based on the module name.\nThe filename will be printed to the console when compiling the source file.\nYou can then move it to a more permanent location."}),"\n",(0,s.jsxs)(t.p,{children:["It can be read in conveniently with ",(0,s.jsx)(t.code,{children:"loadFromFile"})," as an alternative to ",(0,s.jsx)(t.code,{children:"compile"}),"."]}),"\n",(0,s.jsx)(i,{file:"BasicValidators.hs",language:"haskell",title:"Block Title",start:"-- BLOCK6",end:"-- BLOCK7"})]})}function p(e={}){const{wrapper:t}={...(0,n.R)(),...e.components};return t?(0,s.jsx)(t,{...e,children:(0,s.jsx)(d,{...e})}):d(e)}},8453:(e,t,i)=>{i.d(t,{R:()=>o,x:()=>a});var s=i(6540);const n={},r=s.createContext(n);function o(e){const t=s.useContext(r);return s.useMemo((function(){return"function"==typeof e?e(t):{...t,...e}}),[t,e])}function a(e){let t;return t=e.disableParentContext?"function"==typeof e.components?e.components(n):e.components||n:o(e.components),s.createElement(r.Provider,{value:t},e.children)}}}]);