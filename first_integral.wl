(* ::Package:: *)

BeginPackage["FirstIntegral`"]

firstIntegral::usage =
        "FirstIntegral[A, vars] gives a list of first integral for a n dimension differential system with vars, A is a matrix."

Begin["`Private`"]

firstIntegral[A_,vars_]  :=Module[{selectValZero,selectValComplex,
selectValNoComplex,zero, selectValMutipl,selectVal,selectVal2,
selectValNoZero,selectNoMutipl,selectMutipl,group,B,eigensystem,result},
(*Feature extraction*)
eigensystem=Eigensystem[A//Transpose]//Transpose;

(*Remove conjugate eigenvalues and eigenvectors*)
selectValComplex=Select[eigensystem,Head[#[[1]]]===Complex&];
selectValComplex=deleteConjugate[selectValComplex];
selectValNoComplex=Select[eigensystem,Head[#[[1]]]=!=Complex&];
selectVal=Join[selectValComplex,selectValNoComplex];

(*Multiple elementary divisors*)
zero=0.vars;
selectValMutipl=Select[selectVal,#[[2]]==zero&];
selectVal2=Select[selectVal,#[[2]]!=zero&];
selectValComplex=Select[selectVal2,Head[#[[1]]]===Complex&];
selectValZero=Select[selectVal2,#[[1]]==0&];
group=GroupBy[selectValMutipl,First];

selectNoMutipl=selectVal2;

selectMutipl={};
For[i=1,i<=Length[group],i++,
selectNoMutipl=DeleteCases[selectNoMutipl,{group[[i,1,1]],_}];
selectMutipl=Join[selectMutipl,Cases[selectVal2,{group[[i,1,1]],_}]]
];

B=A//Transpose;



result={};(*Set of first integral*)
result=singleComplex[result,selectValComplex,vars];(*Theorem 1.2*)
result=singleMulti[result,B,group,selectVal2,vars];(*Theorem 1.5, 1.8*)
result=singleZero[result,selectNoMutipl,vars];
(*Theorem 1.1 Corollary 1.1*)
If[Length[selectMutipl]==0,
selectValNoZero=Select[selectNoMutipl,#[[1]]!=0&];
result=twoJudgeNoMulti[result,selectValNoZero,vars];
(*Theorem 1.1, 1.3, 1.4*)
 ,
result=twoJudgeMulti[result,selectMutipl,selectNoMutipl,vars,B]
(*Theorem 1.1, 1.3, 1.4, 1.6, 1.7*)
];
Return[result];
]

(*Theorem 1.1 Corollary 1.1*)
singleZero[result_,eigensystem_,vars_]:=Module[{selectValZero,r=result},
selectValZero=Select[eigensystem,#[[1]]==0&];
If[Length[selectValZero]!=0,
For[i=1,i<=Length[selectValZero],i++,
r=Join[r,{selectValZero[[i,2]] . vars}]];
];
Return[r];
]

(*Theorem 1.2*)
singleComplex[result_,selectValComplex_,vars_]:=Module[{r=result},
If[Length[selectValComplex]!=0,
For[i=1,i<=Length[selectValComplex],i++,
r=Join[r,{((Re[selectValComplex[[i,2]]] . vars)^2 + (Im[selectValComplex[[i,2]]] . vars)^2)*Exp[-2*(Re[selectValComplex[[i,1]]]/Im[selectValComplex[[i,1]]])*ArcTan[(Im[selectValComplex[[i,2]]] . vars)/(Re[selectValComplex[[i,2]]] . vars)]]}]]
];

Return[r];
]

deleteConjugate[selectValComplex_]:=Module[{s=selectValComplex},
For[i=1,i<=Length[s],i++,
For[j=i+1,j<=Length[s],j++,
If[s[[j,1]]==Conjugate[s[[i,1]]],
s=Delete[s,j]
]
]
];
Return[s];
]
singleMulti[result_,B_,group_,selectVal_,vars_]:=Module[{r=result},

If[Length[group]!=0,

r=multiCase1[r,B,group,selectVal,vars];

];
Return[r];
];


(*Theorem 1.5*)
multiCase1[result_,B_,group_,selectVal_,vars_]:=Module[{v0,v1,alphe,beta,F1,F2,r=result},
For[i=1,i<=Length[group],i++,

v0=Select[selectVal,#[[1]]==group[[i,1,1]]&][[1,2]];
v1=LinearSolve[B-group[[i,1,1]]*IdentityMatrix[Length[vars]],v0];
If[Head[group[[i,1,1]]]===Complex,
alphe=Re[v0] . vars*Re[v1] . vars+Im[v0] . vars*Im[v1] . vars;
beta=Re[v0] . vars*Im[v1] . vars-Im[v0] . vars*Re[v1] . vars;
F1={((Re[v0] . vars)^2 + (Im[v0] . vars)^2)*Exp[-2*((Re[group[[i,1,1]]]*alphe-Im[group[[i,1,1]]]*beta)/((Re[v0] . vars)^2 + (Im[v0] . vars)^2))]};
F2={ArcTan[Im[v0] . vars/Re[v0] . vars]-((Im[group[[i,1,1]]]*alphe+Re[group[[i,1,1]]]*beta)/((Re[v0] . vars)^2 + (Im[v0] . vars)^2))};
r=Join[r,F1,F2]
,

r=Join[r,{v0 . vars*Exp[-1*group[[i,1,1]]*(v1 . vars/v0 . vars)]}]];
If[Length[group[[i]]]>=2,
r=multiCase2[r,B,group,v0,v1,vars,i]
]

];
Return[r];
]
(*Theorem 1.8*)
multiCase2[result_,B_,group_,v0_,v1_,vars_,i_]:=Module[{V,F,v,f,r=result},
V={v0,v1};
F={v1 . vars/v0 . vars};
If[Head[group[[i,1,1]]]===Complex,

For[j=2,j<=Length[group[[i]]],j++,
v=LinearSolve[B-group[[i,1,1]]*IdentityMatrix[Length[vars]],j*V[[-1]]];


f=multiCalulate[V,F,vars,B,j,i,v0,v];


r=Join[r,{Together[ComplexExpand[Re[f]]]},{Together[ComplexExpand[Im[f]]]}];
F=Join[F,{f}];
V=Join[V,{v}];
]
,


For[j=2,j<=Length[group[[i]]],j++,
v=LinearSolve[B-group[[i,1,1]]*IdentityMatrix[Length[vars]],j*V[[-1]]];
f=multiCalulate[V,F,vars,B,j,i,v0,v];


r=Join[r,{f}];
F=Join[F,{f}];
V=Join[V,{v}];
];];
Return[r];
]

multiCalulate[V_,F_,vars_,B_,j_,i_,v0_,v_]:=Module[{f},
f=v . vars;
For[k=1,k<=j-1,k++,
f=f-Binomial[j-1,k-1]*F[[k]]*V[[j-k+1]] . vars;
];
f=f/v0 . vars;

Return[f];
]
twoJudgeNoMulti[result_,selectVal_,vars_]:=Module[{s1,s2,r=result},
s1=selectVal[[1]];
If[Head[s1[[1]]]===Complex,
For[j=2,j<=Length[selectVal],j++,
s2=selectVal[[j]];
If[Head[s2[[1]]]===Complex,
(*complex and complex*)
r=complexAndComplex[r,s1,s2,vars];
,
(*number and complex*)
r=numberAndComplex[r,s1,s2,vars];
]
]
,
For[j=2,j<=Length[selectVal],j++,
s2=selectVal[[j]];
If[Head[s2[[1]]]===Complex,
(*number and complex*)
r=numberAndComplex[r,s2,s1,vars];
,
(*number and number*)
r=numberAndNumber[r,s1,s2,vars];
]
]
];
Return[r];
]


(*Theorem 1.1*)
numberAndNumber[result_,s1_,s2_,vars_]:=Module[{h1,h2,r=result},
h1=1;
h2=-1*h1*s1[[1]]/s2[[1]];
r=Join[r,{Abs[s1[[2]] . vars]^h1*Abs[s2[[2]] . vars]^h2}];
Return[r];
]
(*Theorem 1.3*)
numberAndComplex[result_,s1_,s2_,vars_]:=Module[{r=result},
(*s1 is complex, s2 is number*)
r=Join[r,{s2[[2]] . vars*Exp[-1*s2[[1]]/Im[s1[[1]]]*ArcTan[(Im[s1[[2]]] . vars)/(Re[s1[[2]]] . vars)]]}];
Return[r];
]
(*Theorem 1.4*)
complexAndComplex[result_,s1_,s2_,vars_]:=Module[{r=result},

r=Join[r,{Im[s1[[1]]]*ArcTan[(Im[s2[[2]]] . vars)/(Re[s2[[2]]] . vars)]-Im[s2[[1]]]*ArcTan[(Im[s1[[2]]] . vars)/(Re[s1[[2]]] . vars)]}];
Return[r];
]

twoJudgeMulti[result_,selectValMulti_,selectValNoMulti_,vars_,B_]:=Module[{s1,s2,v01,v11,v02,v12,r=result},
s1=selectValMulti[[1]];
If[Head[s1[[1]]]===Real,
v01=s1[[2]];
v11=LinearSolve[B-s1[[1]]*IdentityMatrix[Length[vars]],v01];];
(*Theorem 1.7*)


If[s1[[1]]==0,
(*Theorem 1.6*)
For[j=1,j<=Length[selectValNoMulti],j++,
s2=selectValNoMulti[[j]];
If[Head[s2[[1]]]===Complex,
r=Join[r,{((Re[s2[[2]]] . vars)^2+(Im[s2[[2]]] . vars)^2)*Exp[-2*Re[s2[[1]]]*(v11 . vars/v01 . vars)]}];
r=Join[r,{ArcTan[Im[s2[[2]]] . vars/Re[s2[[2]]] . vars]-Im[s2[[1]]]*(v11 . vars/v01 . vars)}];
,
r=Join[r,{s2[[2]] . vars*Exp[-1*s2[[1]]*(v11 . vars/v01 . vars)]}];
];

];
,
(*Theorem 1.1, 1.3, 1.4*)
If[Head[s1[[1]]]===Complex,
For[j=1,j<=Length[selectValNoMulti],j++,
s2=selectValNoMulti[[j]];
If[Head[s2[[1]]]===Complex,
(*complex and complex*)
r=complexAndComplex[r,s1,s2,vars];
,
(*number and complex*)
r=numberAndComplex[r,s1,s2,vars];
]
]
,
For[j=1,j<=Length[selectValNoMulti],j++,
s2=selectValNoMulti[[j]];
If[Head[s2[[1]]]===Complex,
(*number and complex*)
r=numberAndComplex[r,s2,s1,vars];
,
(*number and number*)
r=numberAndNumber[r,s1,s2,vars];
]
]
];
];

If[s1[[1]]==0,
(*Theorem 1.6*)
For[j=2,j<=Length[selectValMulti],j++,
s2=selectValMulti[[j]];
If[Head[s2[[1]]]===Complex,
r=Join[r,{((Re[s2[[2]]] . vars)^2+(Im[s2[[2]]] . vars)^2)*Exp[-2*Re[s2[[1]]]*(v11 . vars/v01 . vars)]}];
r=Join[r,{ArcTan[Im[s2[[2]]] . vars/Re[s2[[2]]] . vars]-Im[s2[[1]]]*(v11 . vars/v01 . vars)}];
,
r=Join[r,{s2[[2]] . vars*Exp[-1*s2[[1]]*(v11 . vars/v01 . vars)]}];
];

];
,
(*Theorem 1.1, 1.3, 1.4*)
If[Head[s1[[1]]]===Complex,
For[j=2,j<=Length[selectValMulti],j++,
s2=selectValMulti[[j]];
If[Head[s2[[1]]]===Complex,
(*complex and complex*)
r=complexAndComplex[r,s1,s2,vars];
,
(*number and complex*)
r=numberAndComplex[r,s1,s2,vars];
]
]
,
For[j=2,j<=Length[selectValMulti],j++,
s2=selectValMulti[[j]];
If[Head[s2[[1]]]===Complex,
(*number and complex*)
r=numberAndComplex[r,s2,s1,vars];
,
(*number and number*)
v02=s2[[2]];
v12=LinearSolve[B-s2[[1]]*IdentityMatrix[Length[vars]],v02];
r=Join[r,{v11 . vars/v01 . vars-v12 . vars/v02 . vars}];
]
]
];
];

Return[r];
]


End[ ]

EndPackage[ ]



