(* ::Package:: *)

BeginPackage[ "checkSafe`"]

  checkSafe::usage = 
    "CheckSafe[L, vars, initial, unsafe] return safe or unsafe for a continus system with vars, L is the first integral list of the system, which is computed
                          by first_integral package."
  checkSafeHybrid::usage =
    "CheckSafeHybrid[L, vars, initial, unsafe,Edge,d,f,G,R] return safe or unsafe for a Hybrid system with vars, L is the first integral list of the system, which is computed
                                    by first_integral package, <Edge,d,f,G,R> is the model of a Hybrid system."





  Begin[ "Private`"]

  checkSafe[L_,vars_,initial_,unsafe_] :=
    Module[ {flag,imin,imax,umin,umax},
      imin={};
      imax={};
      umin={};
      umax={};
      For[i=1,i<=Length[L],i++,
          imin=Join[imin,{FindMinimum[{L[[i]],initial},vars][[1]]}];
          imax=Join[imax,{FindMaximum[{L[[i]],initial},vars][[1]]}];
          umin=Join[umin,{FindMinimum[{L[[i]],unsafe},vars][[1]]}];
          umax=Join[umax,{FindMaximum[{L[[i]],unsafe},vars][[1]]}];
          ];
      flag="undetermined";
      
      For[i=1,i<=Length[L],i++,
        If[umin[[i]]>imax[[i]]|| umax[[i]]<imin[[1]],
          flag="safe";
          Break,
         ];
         ];
      Return[flag]
    ]
    
    
checkSafeHybrid[L_,vars_,initial_,unsafe_,Edge_,d_,f_,G_,R_] :=
 Module[ {flag,imin,imax,umin,umax,unsafeMode},
   unsafeMode={};
   umin={};
   umax={};

   For[i=1,i<=Length[d],i++,
        ExistExpress=Exists[de,unsafe&&d[[i,1]]&&de>0];
        ExistExpress=ReplacePart[ExistExpress,1->vars];
        ExistExpress[[2]]=DeleteCases[ExistExpress[[2]],de>0];
        If[Resolve[ExistExpress]==False,
        ,
       unsafeMode=Join[unsafeMode,{i}];
       ui={};
       ua={};
       For[j=1,j<=Length[L[[i]]],j++,
       
          ui=Join[ui,{FindMinimum[{L[[i,j]],unsafe},vars][[1]]}];
          ua=Join[ua,{FindMaximum[{L[[i,j]],unsafe},vars][[1]]}];
          ];
      umin=Join[umin,{ui}];
      umax=Join[umax,{ua}];
         ];
    ];
    
    flag="undetermined";
    
     For[i=1,i<=Length[d],i++,
        ExistExpress1=Exists[de1,initial&&d[[i,1]]&&de1>0];
       ExistExpress1=ReplacePart[ExistExpress1,1->vars];
       ExistExpress1[[2]]=DeleteCases[ExistExpress1[[2]],de1>0];
    
       If[Resolve[ExistExpress1]==False,
          ,

        ii={};
        ia={};

        For[j=1,j<=Length[L[[i]]],j++,
          ii=Join[ii,{FindMinimum[{L[[i,j]],initial},vars][[1]]}];
          ia=Join[ ia,{FindMaximum[{L[[i,j]],initial},vars][[1]]}];
          ];
       imin={};
       imax={};
       imin=Join[imin,{ii}];
       imax=Join[imax,{ia}];
       mode={i};

       count=1;
      
       While[count<=5 && Length[mode]!=0,
      
            For[k=1,k<=Length[Edge],k++,
                If[Edge[[k,1]]==mode[[1]],

                  mode=Join[mode,{Edge[[k,2]]}];

                  ii={};
                  ia={};
                  For[j=1,j<=Length[L[[Edge[[k,2]]]]],j++,
 
                     Equ=L[[Edge[[k,1]],j]]/.G[[k]];
                     S=Solve[Equ==imin[[1,j]]];

                     GG=Join[G[[k]],S[[1]]];
                     ll=L[[Edge[[k,2]],1]]/.R[[k]];
                     ii1=NMinimize[ll/.GG,vars];
                      ii=Join[ii,{ii1[[1]]}];

                    S=Solve[Equ==imax[[1,j]]];
                    GG=Join[G[[k]],S[[1]]];
 
                    ia1=NMaximize[   ll/.GG,vars];
                     ia=Join[ ia,{ia1[[1]]}];
                     ];

               For[j=1,j<=Length[unsafeMode],j++,
                   If[unsafeMode[[j]]==Edge[[k,2]],
                      flag1=-1;
                      For[h=1,h<=Length[L[[Edge[[k,2]]]]],h++,
                             
                             If[umin[[j,h]]>ia[[h]]|| umax[[j,h]]<ii[[h]],
                               flag1=1;
                                Break,
                                ];
                         ];
                
                If[flag1==-1,
                   Return[flag]
                   ,
                  ];

                ,
                ];
              ];
       
        ,
       ];
    ];
     imin=Join[imin,{ii}];
     imax=Join[imax,{ia}];
     mode=Delete[mode,1];
     imin=Delete[imin,1];
     imax=Delete[imax,1];
     
    count++;
   ];
   
  If[Length[mode]==0,
     flag="Safe";
     Return[flag];
     ,
    ];


   ];
      
        ];
   Return[flag]
    ]
  End[]

EndPackage[]





















































