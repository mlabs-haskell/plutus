"use strict";(self.webpackChunkdocusaurus=self.webpackChunkdocusaurus||[]).push([[8306],{1958:(e,t,i)=>{i.r(t),i.d(t,{assets:()=>c,contentTitle:()=>o,default:()=>h,frontMatter:()=>s,metadata:()=>a,toc:()=>l});var n=i(4848),r=i(8453);const s={sidebar_position:20},o="Profiling the budget usage of Plutus scripts",a={id:"working-with-scripts/profiling-budget-usage",title:"Profiling the budget usage of Plutus scripts",description:"Figuring out why your script takes more CPU or memory units than you expect can be tricky.",source:"@site/docs/working-with-scripts/profiling-budget-usage.md",sourceDirName:"working-with-scripts",slug:"/working-with-scripts/profiling-budget-usage",permalink:"/plutus/master/docs/working-with-scripts/profiling-budget-usage",draft:!1,unlisted:!1,editUrl:"https://github.com/IntersectMBO/plutus/edit/master/docusaurus/docs/working-with-scripts/profiling-budget-usage.md",tags:[],version:"current",sidebarPosition:20,frontMatter:{sidebar_position:20},sidebar:"tutorialSidebar",previous:{title:"Exporting scripts, datums and redeemers",permalink:"/plutus/master/docs/working-with-scripts/exporting-scripts-datums-redeemers"},next:{title:"Architectural decision records",permalink:"/plutus/master/docs/category/architectural-decision-records"}},c={},l=[{value:"Compiling a script for profiling",id:"compiling-a-script-for-profiling",level:2},{value:"Acquiring an executable script",id:"acquiring-an-executable-script",level:2},{value:"Running the script",id:"running-the-script",level:2},{value:"Analyzing the results",id:"analyzing-the-results",level:2}];function u(e){const t={a:"a",blockquote:"blockquote",code:"code",em:"em",h1:"h1",h2:"h2",p:"p",pre:"pre",strong:"strong",...(0,r.R)(),...e.components};return(0,n.jsxs)(n.Fragment,{children:[(0,n.jsx)(t.h1,{id:"profiling-the-budget-usage-of-plutus-scripts",children:"Profiling the budget usage of Plutus scripts"}),"\n",(0,n.jsxs)(t.p,{children:["Figuring out why your script takes more CPU or memory units than you expect can be tricky.\nYou can find out more detail about how these resources are being used in your script by ",(0,n.jsx)(t.em,{children:"profiling"})," it, and viewing the results in a flamegraph."]}),"\n",(0,n.jsx)(t.h2,{id:"compiling-a-script-for-profiling",children:"Compiling a script for profiling"}),"\n",(0,n.jsx)(t.p,{children:"Profiling requires compiling your script differently so that it will emit information that we can use to analyse its performance."}),"\n",(0,n.jsxs)(t.blockquote,{children:["\n",(0,n.jsxs)(t.p,{children:["\ud83d\udccc"," ",(0,n.jsx)(t.strong,{children:"NOTE"})]}),"\n",(0,n.jsx)(t.p,{children:"As with profiling in other languages, this additional instrumentation can affect how your program is optimized, so its behaviour may not be identical to the non-profiled version."}),"\n"]}),"\n",(0,n.jsx)(t.p,{children:"To do this, you need to give a couple of options to the Plutus Tx plugin in the source file where your script is compiled."}),"\n",(0,n.jsx)(t.pre,{children:(0,n.jsx)(t.code,{className:"language-haskell",children:"{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:profile-all #-}\n{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:conservative-optimisation #-}\n"})}),"\n",(0,n.jsx)(t.p,{children:"This instructs the plugin to insert profiling instrumentation for all functions.\nIn the future there may be the option to profile a more targeted set of functions.\nIt also makes sure that any inserted profiling instrumentation code would not be optimized away during PlutusTx compilation."}),"\n",(0,n.jsx)(t.h2,{id:"acquiring-an-executable-script",children:"Acquiring an executable script"}),"\n",(0,n.jsx)(t.p,{children:"Profiling works by seeing how the budget is used as the script runs.\nIt therefore requires an executable script, which means that you need not only the validator script but all the arguments it receives.\nYou can get this fully-applied script from the emulator or from the Cardano node."}),"\n",(0,n.jsx)(t.h2,{id:"running-the-script",children:"Running the script"}),"\n",(0,n.jsxs)(t.p,{children:["You can run the script with the ",(0,n.jsx)(t.code,{children:"uplc"})," executable."]}),"\n",(0,n.jsxs)(t.blockquote,{children:["\n",(0,n.jsxs)(t.p,{children:["\ud83d\udccc"," ",(0,n.jsx)(t.strong,{children:"NOTE"})]}),"\n",(0,n.jsxs)(t.p,{children:["All the executables referred to here can be built from the ",(0,n.jsx)(t.code,{children:"plutus"})," repository using ",(0,n.jsx)(t.code,{children:"cabal build"}),"."]}),"\n"]}),"\n",(0,n.jsx)(t.pre,{children:(0,n.jsx)(t.code,{className:"language-bash",children:"uplc evaluate -i myscript.flat --if flat --trace-mode LogsWithBudgets -o logs\n"})}),"\n",(0,n.jsx)(t.p,{children:"This runs the script using the trace mode that emits budget information, and puts the resulting logs in a file.\nThis will be a CSV file with three columns: a message indicating which function we are entering or exiting; the cumulative CPU used at that time; and the cumulative memory used at that time."}),"\n",(0,n.jsx)(t.h2,{id:"analyzing-the-results",children:"Analyzing the results"}),"\n",(0,n.jsxs)(t.p,{children:["We can then convert the logs into a flamegraph using the standard ",(0,n.jsx)(t.code,{children:"flamegraph.pl"})," tool.\nThe ",(0,n.jsx)(t.code,{children:"traceToStacks"})," executable turns the logs into a format that ",(0,n.jsx)(t.code,{children:"flamegraph.pl"})," understands"]}),"\n",(0,n.jsx)(t.pre,{children:(0,n.jsx)(t.code,{className:"language-bash",children:"cat logs | traceToStacks | flamegraph.pl > cpu.svg\ncat logs | traceToStacks --column 2 | flamegraph.pl > mem.svg\n"})}),"\n",(0,n.jsxs)(t.p,{children:["Since ",(0,n.jsx)(t.code,{children:"flamegraph.pl"})," can only handle one metric at a time, ",(0,n.jsx)(t.code,{children:"traceToStacks"})," has a ",(0,n.jsx)(t.code,{children:"--column"})," argument to select the other column if you want to get a memory flamegraph."]}),"\n",(0,n.jsx)(t.p,{children:"You can then view the resulting SVGs in a viewer of your choice, such as a web browser."}),"\n",(0,n.jsxs)(t.p,{children:["Alternatively, there are other, more powerful, tools that understand the format produced by ",(0,n.jsx)(t.code,{children:"traceToStacks"}),", such as ",(0,n.jsx)(t.a,{href:"https://www.speedscope.app/",children:"speedscope"}),"."]})]})}function h(e={}){const{wrapper:t}={...(0,r.R)(),...e.components};return t?(0,n.jsx)(t,{...e,children:(0,n.jsx)(u,{...e})}):u(e)}},8453:(e,t,i)=>{i.d(t,{R:()=>o,x:()=>a});var n=i(6540);const r={},s=n.createContext(r);function o(e){const t=n.useContext(s);return n.useMemo((function(){return"function"==typeof e?e(t):{...t,...e}}),[t,e])}function a(e){let t;return t=e.disableParentContext?"function"==typeof e.components?e.components(r):e.components||r:o(e.components),n.createElement(s.Provider,{value:t},e.children)}}}]);