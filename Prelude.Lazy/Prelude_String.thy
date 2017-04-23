theory Prelude_String
imports "$HETS_ISABELLE_LIB/MainHC"
uses "$HETS_ISABELLE_LIB/prelude"
begin

ML "Header.initialize
    [\"ga_subt_reflexive\", \"ga_subt_transitive\",
     \"ga_subt_inj_proj\", \"ga_inj_transitive\",
     \"ga_subt_Int_XLt_Rat\", \"ga_subt_Nat_XLt_Int\",
     \"ga_subt_Pos_XLt_Nat\", \"Comp1\", \"IdDef\", \"FlipDef\",
     \"FstDef\", \"SndDef\", \"CurryDef\", \"UncurryDef\", \"NotFalse\",
     \"NotTrue\", \"AndFalse\", \"AndTrue\", \"AndSym\", \"OrDef\",
     \"OtherwiseDef\", \"NotFalse1\", \"NotTrue1\", \"notNot1\",
     \"notNot2\", \"EqualTDef\", \"EqualSymDef\", \"EqualReflex\",
     \"EqualTransT\", \"DiffDef\", \"DiffSymDef\", \"DiffTDef\",
     \"DiffFDef\", \"TE1\", \"TE2\", \"TE3\", \"TE4\", \"IUE1\",
     \"IUE2\", \"IBE1\", \"IBE2\", \"IBE3\", \"IBE4\", \"IBE5\",
     \"IBE6\", \"IBE7\", \"IBE8\", \"IOE01\", \"IOE02\", \"IOE03\",
     \"IOE04\", \"IOE05\", \"IOE06\", \"IOE07\", \"IOE08\", \"IOE09\",
     \"LeIrreflexivity\", \"LeTAsymmetry\", \"LeTTransitive\",
     \"LeTTotal\", \"GeDef\", \"GeIrreflexivity\", \"GeTAsymmetry\",
     \"GeTTransitive\", \"GeTTotal\", \"LeqDef\", \"LeqReflexivity\",
     \"LeqTTransitive\", \"LeqTTotal\", \"GeqDef\", \"GeqReflexivity\",
     \"GeqTTransitive\", \"GeqTTotal\", \"EqTSOrdRel\", \"EqFSOrdRel\",
     \"EqTOrdRel\", \"EqFOrdRel\", \"EqTOrdTSubstE\", \"EqTOrdFSubstE\",
     \"EqTOrdTSubstD\", \"EqTOrdFSubstD\", \"LeTGeFEqFRel\",
     \"LeFGeTEqTRel\", \"LeTGeTRel\", \"LeFGeFRel\", \"LeqTGetTRel\",
     \"LeqFGetFRel\", \"GeTLeTRel\", \"GeFLeFRel\", \"GeqTLeqTRel\",
     \"GeqFLeqFRel\", \"LeqTGeFRel\", \"LeqFGeTRel\", \"GeTLeFEqFRel\",
     \"GeFLeTEqTRel\", \"GeqTLeFRel\", \"GeqFLeTRel\",
     \"LeqTLeTEqTRel\", \"LeqFLeFEqFRel\", \"GeqTGeTEqTRel\",
     \"GeqFGeFEqFRel\", \"LeTGeqFRel\", \"GeTLeqFRel\", \"LeLeqDiff\",
     \"CmpLTDef\", \"CmpEQDef\", \"CmpGTDef\", \"MaxYDef\", \"MaxXDef\",
     \"MinXDef\", \"MinYDef\", \"MaxSym\", \"MinSym\", \"TO1\", \"TO2\",
     \"TO3\", \"TO4\", \"TO5\", \"TO6\", \"TO7\", \"IUO01\", \"IUO02\",
     \"IUO03\", \"IUO04\", \"IUO05\", \"IUO06\", \"IUO07\", \"IOO13\",
     \"IOO14\", \"IOO15\", \"IOO16\", \"IOO17\", \"IOO18\", \"IOO19\",
     \"IOO20\", \"IOO21\", \"IOO22\", \"IOO23\", \"IOO24\", \"IOO25\",
     \"IOO26\", \"IOO27\", \"IOO28\", \"IOO29\", \"IOO30\", \"IOO31\",
     \"IOO32\", \"IOO33\", \"IBO5\", \"IBO6\", \"IBO7\", \"IBO8\",
     \"IBO9\", \"IBO10\", \"IBO11\", \"IBO12\", \"NotDefHead\",
     \"HeadDef\", \"NotDefTail\", \"TailDef\", \"FoldrNil\",
     \"FoldrCons\", \"FoldlNil\", \"FoldlCons\", \"MapNil\",
     \"MapCons\", \"XPlusXPlusNil\", \"XPlusXPlusCons\", \"FilterNil\",
     \"FilterConsT\", \"FilterConsF\", \"ZipNil\", \"ZipConsNil\",
     \"ZipConsCons\", \"UnzipNil\", \"UnzipCons\", \"ILE01\", \"ILE02\",
     \"ILO01\", \"ILO02\", \"ILO03\", \"ILO04\", \"ILO05\", \"ILO06\",
     \"ILO07\", \"ILO08\", \"ILO09\", \"ILO10\", \"ILO11\", \"ILO12\",
     \"ILO13\", \"ILO14\", \"ILO15\", \"ILO16\", \"ILO17\", \"ILO18\",
     \"ILO19\", \"ILO20\", \"ILO21\", \"ILO22\", \"FoldlDecomp\",
     \"MapDecomp\", \"MapFunctor\", \"FilterProm\", \"InitNil\",
     \"InitConsNil\", \"InitConsCons\", \"LastNil\", \"LastConsNil\",
     \"LastConsCons\", \"NullNil\", \"NullCons\", \"ReverseNil\",
     \"ReverseCons\", \"Foldr1Nil\", \"Foldr1ConsNil\",
     \"Foldr1ConsCons\", \"Foldl1Nil\", \"Foldl1ConsNil\",
     \"Foldl1ConsCons\", \"ScanlNil\", \"ScanlCons\", \"Scanl1Nil\",
     \"Scanl1Cons\", \"ScanrNil\", \"ScanrCons\", \"Scanr1Nil\",
     \"Scanr1ConsNil\", \"Scanr1ConsCons\", \"ScanlProperty\",
     \"ScanrProperty\", \"ConcatDef\", \"ConcatMapDef\", \"MaximunNil\",
     \"MaximumDef\", \"MinimunNil\", \"MinimumDef\", \"TakeWhileNil\",
     \"TakeWhileConsT\", \"TakeWhileConsF\", \"DropWhileNil\",
     \"DropWhileConsT\", \"DropWhileConsF\", \"SpanNil\", \"SpanConsT\",
     \"SpanConsF\", \"SpanThm\", \"BreakDef\", \"BreakThm\",
     \"InsertNil\", \"InsertCons1\", \"InsertCons2\", \"DeleteNil\",
     \"DeleteConsT\", \"DeleteConsF\", \"SelectT\", \"SelectF\",
     \"Partition\", \"PartitionProp\", \"ga_selector_pre\",
     \"ga_injective_suc\", \"ga_disjoint_0_suc\",
     \"ga_selector_undef_pre_0\", \"X1_def_Nat\", \"X2_def_Nat\",
     \"X3_def_Nat\", \"X4_def_Nat\", \"X5_def_Nat\", \"X6_def_Nat\",
     \"X7_def_Nat\", \"X8_def_Nat\", \"X9_def_Nat\", \"decimal_def\",
     \"ga_comm___XPlus__\", \"ga_assoc___XPlus__\",
     \"ga_right_unit___XPlus__\", \"ga_left_unit___XPlus__\",
     \"ga_left_comm___XPlus__\", \"ga_comm___Xx__\",
     \"ga_assoc___Xx__\", \"ga_right_unit___Xx__\",
     \"ga_left_unit___Xx__\", \"ga_left_comm___Xx__\", \"ga_comm_min\",
     \"ga_assoc_min\", \"ga_left_comm_min\", \"ga_comm_max\",
     \"ga_assoc_max\", \"ga_right_unit_max\", \"ga_left_unit_max\",
     \"ga_left_comm_max\", \"leq_def1_Nat\", \"dvd_def_Nat\",
     \"leq_def2_Nat\", \"leq_def3_Nat\", \"geq_def_Nat\",
     \"less_def_Nat\", \"greater_def_Nat\", \"even_0_Nat\",
     \"even_suc_Nat\", \"odd_def_Nat\", \"factorial_0\",
     \"factorial_suc\", \"add_0_Nat\", \"add_suc_Nat\", \"mult_0_Nat\",
     \"mult_suc_Nat\", \"power_0_Nat\", \"power_suc_Nat\",
     \"min_def_Nat\", \"max_def_Nat\", \"subTotal_def1_Nat\",
     \"subTotal_def2_Nat\", \"sub_dom_Nat\", \"sub_def_Nat\",
     \"divide_dom_Nat\", \"divide_0_Nat\", \"divide_Pos_Nat\",
     \"div_dom_Nat\", \"div_Nat\", \"mod_dom_Nat\", \"mod_Nat\",
     \"distr1_Nat\", \"distr2_Nat\", \"Pos_def\", \"X1_as_Pos_def\",
     \"min_0\", \"div_mod_Nat\", \"power_Nat\", \"ga_selector_ord\",
     \"chr_dom\", \"chr_ord_inverse\", \"slash_000\", \"slash_001\",
     \"slash_002\", \"slash_003\", \"slash_004\", \"slash_005\",
     \"slash_006\", \"slash_007\", \"slash_008\", \"slash_009\",
     \"slash_010\", \"slash_011\", \"slash_012\", \"slash_013\",
     \"slash_014\", \"slash_015\", \"slash_016\", \"slash_017\",
     \"slash_018\", \"slash_019\", \"slash_020\", \"slash_021\",
     \"slash_022\", \"slash_023\", \"slash_024\", \"slash_025\",
     \"slash_026\", \"slash_027\", \"slash_028\", \"slash_029\",
     \"slash_030\", \"slash_031\", \"slash_032\", \"slash_033\",
     \"slash_034\", \"slash_035\", \"slash_036\", \"slash_037\",
     \"slash_038\", \"slash_039\", \"slash_040\", \"slash_041\",
     \"slash_042\", \"slash_043\", \"slash_044\", \"slash_045\",
     \"slash_046\", \"slash_047\", \"slash_048\", \"slash_049\",
     \"slash_050\", \"slash_051\", \"slash_052\", \"slash_053\",
     \"slash_054\", \"slash_055\", \"slash_056\", \"slash_057\",
     \"slash_058\", \"slash_059\", \"slash_060\", \"slash_061\",
     \"slash_062\", \"slash_063\", \"slash_064\", \"slash_065\",
     \"slash_066\", \"slash_067\", \"slash_068\", \"slash_069\",
     \"slash_070\", \"slash_071\", \"slash_072\", \"slash_073\",
     \"slash_074\", \"slash_075\", \"slash_076\", \"slash_077\",
     \"slash_078\", \"slash_079\", \"slash_080\", \"slash_081\",
     \"slash_082\", \"slash_083\", \"slash_084\", \"slash_085\",
     \"slash_086\", \"slash_087\", \"slash_088\", \"slash_089\",
     \"slash_090\", \"slash_091\", \"slash_092\", \"slash_093\",
     \"slash_094\", \"slash_095\", \"slash_096\", \"slash_097\",
     \"slash_098\", \"slash_099\", \"slash_100\", \"slash_101\",
     \"slash_102\", \"slash_103\", \"slash_104\", \"slash_105\",
     \"slash_106\", \"slash_107\", \"slash_108\", \"slash_109\",
     \"slash_110\", \"slash_111\", \"slash_112\", \"slash_113\",
     \"slash_114\", \"slash_115\", \"slash_116\", \"slash_117\",
     \"slash_118\", \"slash_119\", \"slash_120\", \"slash_121\",
     \"slash_122\", \"slash_123\", \"slash_124\", \"slash_125\",
     \"slash_126\", \"slash_127\", \"slash_128\", \"slash_129\",
     \"slash_130\", \"slash_131\", \"slash_132\", \"slash_133\",
     \"slash_134\", \"slash_135\", \"slash_136\", \"slash_137\",
     \"slash_138\", \"slash_139\", \"slash_140\", \"slash_141\",
     \"slash_142\", \"slash_143\", \"slash_144\", \"slash_145\",
     \"slash_146\", \"slash_147\", \"slash_148\", \"slash_149\",
     \"slash_150\", \"slash_151\", \"slash_152\", \"slash_153\",
     \"slash_154\", \"slash_155\", \"slash_156\", \"slash_157\",
     \"slash_158\", \"slash_159\", \"slash_160\", \"slash_161\",
     \"slash_162\", \"slash_163\", \"slash_164\", \"slash_165\",
     \"slash_166\", \"slash_167\", \"slash_168\", \"slash_169\",
     \"slash_170\", \"slash_171\", \"slash_172\", \"slash_173\",
     \"slash_174\", \"slash_175\", \"slash_176\", \"slash_177\",
     \"slash_178\", \"slash_179\", \"slash_180\", \"slash_181\",
     \"slash_182\", \"slash_183\", \"slash_184\", \"slash_185\",
     \"slash_186\", \"slash_187\", \"slash_188\", \"slash_189\",
     \"slash_190\", \"slash_191\", \"slash_192\", \"slash_193\",
     \"slash_194\", \"slash_195\", \"slash_196\", \"slash_197\",
     \"slash_198\", \"slash_199\", \"slash_200\", \"slash_201\",
     \"slash_202\", \"slash_203\", \"slash_204\", \"slash_205\",
     \"slash_206\", \"slash_207\", \"slash_208\", \"slash_209\",
     \"slash_210\", \"slash_211\", \"slash_212\", \"slash_213\",
     \"slash_214\", \"slash_215\", \"slash_216\", \"slash_217\",
     \"slash_218\", \"slash_219\", \"slash_220\", \"slash_221\",
     \"slash_222\", \"slash_223\", \"slash_224\", \"slash_225\",
     \"slash_226\", \"slash_227\", \"slash_228\", \"slash_229\",
     \"slash_230\", \"slash_231\", \"slash_232\", \"slash_233\",
     \"slash_234\", \"slash_235\", \"slash_236\", \"slash_237\",
     \"slash_238\", \"slash_239\", \"slash_240\", \"slash_241\",
     \"slash_242\", \"slash_243\", \"slash_244\", \"slash_245\",
     \"slash_246\", \"slash_247\", \"slash_248\", \"slash_249\",
     \"slash_250\", \"slash_251\", \"slash_252\", \"slash_253\",
     \"slash_254\", \"slash_255\", \"printable_32\", \"printable_33\",
     \"printable_34\", \"printable_35\", \"printable_36\",
     \"printable_37\", \"printable_38\", \"printable_39\",
     \"printable_40\", \"printable_41\", \"printable_42\",
     \"printable_43\", \"printable_44\", \"printable_45\",
     \"printable_46\", \"printable_47\", \"printable_48\",
     \"printable_49\", \"printable_50\", \"printable_51\",
     \"printable_52\", \"printable_53\", \"printable_54\",
     \"printable_55\", \"printable_56\", \"printable_57\",
     \"printable_58\", \"printable_59\", \"printable_60\",
     \"printable_61\", \"printable_62\", \"printable_63\",
     \"printable_64\", \"printable_65\", \"printable_66\",
     \"printable_67\", \"printable_68\", \"printable_69\",
     \"printable_70\", \"printable_71\", \"printable_72\",
     \"printable_73\", \"printable_74\", \"printable_75\",
     \"printable_76\", \"printable_77\", \"printable_78\",
     \"printable_79\", \"printable_80\", \"printable_81\",
     \"printable_82\", \"printable_83\", \"printable_84\",
     \"printable_85\", \"printable_86\", \"printable_87\",
     \"printable_88\", \"printable_89\", \"printable_90\",
     \"printable_91\", \"printable_92\", \"printable_93\",
     \"printable_94\", \"printable_95\", \"printable_96\",
     \"printable_97\", \"printable_98\", \"printable_99\",
     \"printable_100\", \"printable_101\", \"printable_102\",
     \"printable_103\", \"printable_104\", \"printable_105\",
     \"printable_106\", \"printable_107\", \"printable_108\",
     \"printable_109\", \"printable_110\", \"printable_111\",
     \"printable_112\", \"printable_113\", \"printable_114\",
     \"printable_115\", \"printable_116\", \"printable_117\",
     \"printable_118\", \"printable_119\", \"printable_120\",
     \"printable_121\", \"printable_122\", \"printable_123\",
     \"printable_124\", \"printable_125\", \"printable_126\",
     \"printable_160\", \"printable_161\", \"printable_162\",
     \"printable_163\", \"printable_164\", \"printable_165\",
     \"printable_166\", \"printable_167\", \"printable_168\",
     \"printable_169\", \"printable_170\", \"printable_171\",
     \"printable_172\", \"printable_173\", \"printable_174\",
     \"printable_175\", \"printable_176\", \"printable_177\",
     \"printable_178\", \"printable_179\", \"printable_180\",
     \"printable_181\", \"printable_182\", \"printable_183\",
     \"printable_184\", \"printable_185\", \"printable_186\",
     \"printable_187\", \"printable_188\", \"printable_189\",
     \"printable_190\", \"printable_191\", \"printable_192\",
     \"printable_193\", \"printable_194\", \"printable_195\",
     \"printable_196\", \"printable_197\", \"printable_198\",
     \"printable_199\", \"printable_200\", \"printable_201\",
     \"printable_202\", \"printable_203\", \"printable_204\",
     \"printable_205\", \"printable_206\", \"printable_207\",
     \"printable_208\", \"printable_209\", \"printable_210\",
     \"printable_211\", \"printable_212\", \"printable_213\",
     \"printable_214\", \"printable_215\", \"printable_216\",
     \"printable_217\", \"printable_218\", \"printable_219\",
     \"printable_220\", \"printable_221\", \"printable_222\",
     \"printable_223\", \"printable_224\", \"printable_225\",
     \"printable_226\", \"printable_227\", \"printable_228\",
     \"printable_229\", \"printable_230\", \"printable_231\",
     \"printable_232\", \"printable_233\", \"printable_234\",
     \"printable_235\", \"printable_236\", \"printable_237\",
     \"printable_238\", \"printable_239\", \"printable_240\",
     \"printable_241\", \"printable_242\", \"printable_243\",
     \"printable_244\", \"printable_245\", \"printable_246\",
     \"printable_247\", \"printable_248\", \"printable_249\",
     \"printable_250\", \"printable_251\", \"printable_252\",
     \"printable_253\", \"printable_254\", \"printable_255\",
     \"isLetter_def\", \"isDigit_def\", \"isPrintable_def\",
     \"slash_o000\", \"slash_o001\", \"slash_o002\", \"slash_o003\",
     \"slash_o004\", \"slash_o005\", \"slash_o006\", \"slash_o007\",
     \"slash_o010\", \"slash_o011\", \"slash_o012\", \"slash_o013\",
     \"slash_o014\", \"slash_o015\", \"slash_o016\", \"slash_o017\",
     \"slash_o020\", \"slash_o021\", \"slash_o022\", \"slash_o023\",
     \"slash_o024\", \"slash_o025\", \"slash_o026\", \"slash_o027\",
     \"slash_o030\", \"slash_o031\", \"slash_o032\", \"slash_o033\",
     \"slash_o034\", \"slash_o035\", \"slash_o036\", \"slash_o037\",
     \"slash_o040\", \"slash_o041\", \"slash_o042\", \"slash_o043\",
     \"slash_o044\", \"slash_o045\", \"slash_o046\", \"slash_o047\",
     \"slash_o050\", \"slash_o051\", \"slash_o052\", \"slash_o053\",
     \"slash_o054\", \"slash_o055\", \"slash_o056\", \"slash_o057\",
     \"slash_o060\", \"slash_o061\", \"slash_o062\", \"slash_o063\",
     \"slash_o064\", \"slash_o065\", \"slash_o066\", \"slash_o067\",
     \"slash_o070\", \"slash_o071\", \"slash_o072\", \"slash_o073\",
     \"slash_o074\", \"slash_o075\", \"slash_o076\", \"slash_o077\",
     \"slash_o100\", \"slash_o101\", \"slash_o102\", \"slash_o103\",
     \"slash_o104\", \"slash_o105\", \"slash_o106\", \"slash_o107\",
     \"slash_o110\", \"slash_o111\", \"slash_o112\", \"slash_o113\",
     \"slash_o114\", \"slash_o115\", \"slash_o116\", \"slash_o117\",
     \"slash_o120\", \"slash_o121\", \"slash_o122\", \"slash_o123\",
     \"slash_o124\", \"slash_o125\", \"slash_o126\", \"slash_o127\",
     \"slash_o130\", \"slash_o131\", \"slash_o132\", \"slash_o133\",
     \"slash_o134\", \"slash_o135\", \"slash_o136\", \"slash_o137\",
     \"slash_o140\", \"slash_o141\", \"slash_o142\", \"slash_o143\",
     \"slash_o144\", \"slash_o145\", \"slash_o146\", \"slash_o147\",
     \"slash_o150\", \"slash_o151\", \"slash_o152\", \"slash_o153\",
     \"slash_o154\", \"slash_o155\", \"slash_o156\", \"slash_o157\",
     \"slash_o160\", \"slash_o161\", \"slash_o162\", \"slash_o163\",
     \"slash_o164\", \"slash_o165\", \"slash_o166\", \"slash_o167\",
     \"slash_o170\", \"slash_o171\", \"slash_o172\", \"slash_o173\",
     \"slash_o174\", \"slash_o175\", \"slash_o176\", \"slash_o177\",
     \"slash_o200\", \"slash_o201\", \"slash_o202\", \"slash_o203\",
     \"slash_o204\", \"slash_o205\", \"slash_o206\", \"slash_o207\",
     \"slash_o210\", \"slash_o211\", \"slash_o212\", \"slash_o213\",
     \"slash_o214\", \"slash_o215\", \"slash_o216\", \"slash_o217\",
     \"slash_o220\", \"slash_o221\", \"slash_o222\", \"slash_o223\",
     \"slash_o224\", \"slash_o225\", \"slash_o226\", \"slash_o227\",
     \"slash_o230\", \"slash_o231\", \"slash_o232\", \"slash_o233\",
     \"slash_o234\", \"slash_o235\", \"slash_o236\", \"slash_o237\",
     \"slash_o240\", \"slash_o241\", \"slash_o242\", \"slash_o243\",
     \"slash_o244\", \"slash_o245\", \"slash_o246\", \"slash_o247\",
     \"slash_o250\", \"slash_o251\", \"slash_o252\", \"slash_o253\",
     \"slash_o254\", \"slash_o255\", \"slash_o256\", \"slash_o257\",
     \"slash_o260\", \"slash_o261\", \"slash_o262\", \"slash_o263\",
     \"slash_o264\", \"slash_o265\", \"slash_o266\", \"slash_o267\",
     \"slash_o270\", \"slash_o271\", \"slash_o272\", \"slash_o273\",
     \"slash_o274\", \"slash_o275\", \"slash_o276\", \"slash_o277\",
     \"slash_o300\", \"slash_o301\", \"slash_o302\", \"slash_o303\",
     \"slash_o304\", \"slash_o305\", \"slash_o306\", \"slash_o307\",
     \"slash_o310\", \"slash_o311\", \"slash_o312\", \"slash_o313\",
     \"slash_o314\", \"slash_o315\", \"slash_o316\", \"slash_o317\",
     \"slash_o320\", \"slash_o321\", \"slash_o322\", \"slash_o323\",
     \"slash_o324\", \"slash_o325\", \"slash_o326\", \"slash_o327\",
     \"slash_o330\", \"slash_o331\", \"slash_o332\", \"slash_o333\",
     \"slash_o334\", \"slash_o335\", \"slash_o336\", \"slash_o337\",
     \"slash_o340\", \"slash_o341\", \"slash_o342\", \"slash_o343\",
     \"slash_o344\", \"slash_o345\", \"slash_o346\", \"slash_o347\",
     \"slash_o350\", \"slash_o351\", \"slash_o352\", \"slash_o353\",
     \"slash_o354\", \"slash_o355\", \"slash_o356\", \"slash_o357\",
     \"slash_o360\", \"slash_o361\", \"slash_o362\", \"slash_o363\",
     \"slash_o364\", \"slash_o365\", \"slash_o366\", \"slash_o367\",
     \"slash_o370\", \"slash_o371\", \"slash_o372\", \"slash_o373\",
     \"slash_o374\", \"slash_o375\", \"slash_o376\", \"slash_o377\",
     \"slash_x00\", \"slash_x01\", \"slash_x02\", \"slash_x03\",
     \"slash_x04\", \"slash_x05\", \"slash_x06\", \"slash_x07\",
     \"slash_x08\", \"slash_x09\", \"slash_x0A\", \"slash_x0B\",
     \"slash_x0C\", \"slash_x0D\", \"slash_x0E\", \"slash_x0F\",
     \"slash_x10\", \"slash_x11\", \"slash_x12\", \"slash_x13\",
     \"slash_x14\", \"slash_x15\", \"slash_x16\", \"slash_x17\",
     \"slash_x18\", \"slash_x19\", \"slash_x1A\", \"slash_x1B\",
     \"slash_x1C\", \"slash_x1D\", \"slash_x1E\", \"slash_x1F\",
     \"slash_x20\", \"slash_x21\", \"slash_x22\", \"slash_x23\",
     \"slash_x24\", \"slash_x25\", \"slash_x26\", \"slash_x27\",
     \"slash_x28\", \"slash_x29\", \"slash_x2A\", \"slash_x2B\",
     \"slash_x2C\", \"slash_x2D\", \"slash_x2E\", \"slash_x2F\",
     \"slash_x30\", \"slash_x31\", \"slash_x32\", \"slash_x33\",
     \"slash_x34\", \"slash_x35\", \"slash_x36\", \"slash_x37\",
     \"slash_x38\", \"slash_x39\", \"slash_x3A\", \"slash_x3B\",
     \"slash_x3C\", \"slash_x3D\", \"slash_x3E\", \"slash_x3F\",
     \"slash_x40\", \"slash_x41\", \"slash_x42\", \"slash_x43\",
     \"slash_x44\", \"slash_x45\", \"slash_x46\", \"slash_x47\",
     \"slash_x48\", \"slash_x49\", \"slash_x4A\", \"slash_x4B\",
     \"slash_x4C\", \"slash_x4D\", \"slash_x4E\", \"slash_x4F\",
     \"slash_x50\", \"slash_x51\", \"slash_x52\", \"slash_x53\",
     \"slash_x54\", \"slash_x55\", \"slash_x56\", \"slash_x57\",
     \"slash_x58\", \"slash_x59\", \"slash_x5A\", \"slash_x5B\",
     \"slash_x5C\", \"slash_x5D\", \"slash_x5E\", \"slash_x5F\",
     \"slash_x60\", \"slash_x61\", \"slash_x62\", \"slash_x63\",
     \"slash_x64\", \"slash_x65\", \"slash_x66\", \"slash_x67\",
     \"slash_x68\", \"slash_x69\", \"slash_x6A\", \"slash_x6B\",
     \"slash_x6C\", \"slash_x6D\", \"slash_x6E\", \"slash_x6F\",
     \"slash_x70\", \"slash_x71\", \"slash_x72\", \"slash_x73\",
     \"slash_x74\", \"slash_x75\", \"slash_x76\", \"slash_x77\",
     \"slash_x78\", \"slash_x79\", \"slash_x7A\", \"slash_x7B\",
     \"slash_x7C\", \"slash_x7D\", \"slash_x7E\", \"slash_x7F\",
     \"slash_x80\", \"slash_x81\", \"slash_x82\", \"slash_x83\",
     \"slash_x84\", \"slash_x85\", \"slash_x86\", \"slash_x87\",
     \"slash_x88\", \"slash_x89\", \"slash_x8A\", \"slash_x8B\",
     \"slash_x8C\", \"slash_x8D\", \"slash_x8E\", \"slash_x8F\",
     \"slash_x90\", \"slash_x91\", \"slash_x92\", \"slash_x93\",
     \"slash_x94\", \"slash_x95\", \"slash_x96\", \"slash_x97\",
     \"slash_x98\", \"slash_x99\", \"slash_x9A\", \"slash_x9B\",
     \"slash_x9C\", \"slash_x9D\", \"slash_x9E\", \"slash_x9F\",
     \"slash_xA0\", \"slash_xA1\", \"slash_xA2\", \"slash_xA3\",
     \"slash_xA4\", \"slash_xA5\", \"slash_xA6\", \"slash_xA7\",
     \"slash_xA8\", \"slash_xA9\", \"slash_xAA\", \"slash_xAB\",
     \"slash_xAC\", \"slash_xAD\", \"slash_xAE\", \"slash_xAF\",
     \"slash_xB0\", \"slash_xB1\", \"slash_xB2\", \"slash_xB3\",
     \"slash_xB4\", \"slash_xB5\", \"slash_xB6\", \"slash_xB7\",
     \"slash_xB8\", \"slash_xB9\", \"slash_xBA\", \"slash_xBB\",
     \"slash_xBC\", \"slash_xBD\", \"slash_xBE\", \"slash_xBF\",
     \"slash_xC0\", \"slash_xC1\", \"slash_xC2\", \"slash_xC3\",
     \"slash_xC4\", \"slash_xC5\", \"slash_xC6\", \"slash_xC7\",
     \"slash_xC8\", \"slash_xC9\", \"slash_xCA\", \"slash_xCB\",
     \"slash_xCC\", \"slash_xCD\", \"slash_xCE\", \"slash_xCF\",
     \"slash_xD0\", \"slash_xD1\", \"slash_xD2\", \"slash_xD3\",
     \"slash_xD4\", \"slash_xD5\", \"slash_xD6\", \"slash_xD7\",
     \"slash_xD8\", \"slash_xD9\", \"slash_xDA\", \"slash_xDB\",
     \"slash_xDC\", \"slash_xDD\", \"slash_xDE\", \"slash_xDF\",
     \"slash_xE0\", \"slash_xE1\", \"slash_xE2\", \"slash_xE3\",
     \"slash_xE4\", \"slash_xE5\", \"slash_xE6\", \"slash_xE7\",
     \"slash_xE8\", \"slash_xE9\", \"slash_xEA\", \"slash_xEB\",
     \"slash_xEC\", \"slash_xED\", \"slash_xEE\", \"slash_xEF\",
     \"slash_xF0\", \"slash_xF1\", \"slash_xF2\", \"slash_xF3\",
     \"slash_xF4\", \"slash_xF5\", \"slash_xF6\", \"slash_xF7\",
     \"slash_xF8\", \"slash_xF9\", \"slash_xFA\", \"slash_xFB\",
     \"slash_xFC\", \"slash_xFD\", \"slash_xFE\", \"slash_xFF\",
     \"NUL_def\", \"SOH_def\", \"SYX_def\", \"ETX_def\", \"EOT_def\",
     \"ENQ_def\", \"ACK_def\", \"BEL_def\", \"BS_def\", \"HT_def\",
     \"LF_def\", \"VT_def\", \"FF_def\", \"CR_def\", \"SO_def\",
     \"SI_def\", \"DLE_def\", \"DC1_def\", \"DC2_def\", \"DC3_def\",
     \"DC4_def\", \"NAK_def\", \"SYN_def\", \"ETB_def\", \"CAN_def\",
     \"EM_def\", \"SUB_def\", \"ESC_def\", \"FS_def\", \"GS_def\",
     \"RS_def\", \"US_def\", \"SP_def\", \"DEL_def\", \"NL_def\",
     \"NP_def\", \"slash_n\", \"slash_t\", \"slash_v\", \"slash_b\",
     \"slash_r\", \"slash_f\", \"slash_a\", \"slash_quest\",
     \"ga_generated_Int\", \"equality_Int\", \"Nat2Int_embedding\",
     \"ga_comm___XPlus___80\", \"ga_assoc___XPlus___86\",
     \"ga_right_unit___XPlus___77\", \"ga_left_unit___XPlus___78\",
     \"ga_left_comm___XPlus___85\", \"ga_comm___Xx___79\",
     \"ga_assoc___Xx___84\", \"ga_right_unit___Xx___75\",
     \"ga_left_unit___Xx___76\", \"ga_left_comm___Xx___83\",
     \"ga_comm_min_82\", \"ga_comm_max_81\", \"ga_assoc_min_90\",
     \"ga_assoc_max_88\", \"ga_left_comm_min_89\",
     \"ga_left_comm_max_87\", \"leq_def_Int\", \"geq_def_Int\",
     \"less_def_Int\", \"greater_def_Int\", \"even_def_Int\",
     \"odd_def_Int\", \"odd_alt_Int\", \"neg_def_Int\",
     \"sign_def_Int\", \"abs_def_Int\", \"add_def_Int\",
     \"mult_def_Int\", \"sub_def_Int\", \"min_def_Int\",
     \"max_def_Int\", \"power_neg1_Int\", \"power_others_Int\",
     \"divide_dom2_Int\", \"divide_alt_Int\", \"divide_Int\",
     \"div_dom_Int\", \"div_Int\", \"quot_dom_Int\", \"quot_neg_Int\",
     \"quot_nonneg_Int\", \"rem_dom_Int\", \"quot_rem_Int\",
     \"rem_nonneg_Int\", \"mod_dom_Int\", \"mod_Int\", \"distr1_Int\",
     \"distr2_Int\", \"Int_Nat_sub_compat\", \"abs_decomp_Int\",
     \"mod_abs_Int\", \"div_mod_Int\", \"quot_abs_Int\",
     \"rem_abs_Int\", \"quot_rem_Int_123\", \"power_Int\",
     \"ga_generated_Rat\", \"equality_Rat\", \"Int2Rat_embedding\",
     \"ga_comm___XPlus___139\", \"ga_assoc___XPlus___145\",
     \"ga_right_unit___XPlus___136\", \"ga_left_unit___XPlus___137\",
     \"ga_left_comm___XPlus___144\", \"ga_comm___Xx___138\",
     \"ga_assoc___Xx___143\", \"ga_right_unit___Xx___134\",
     \"ga_left_unit___Xx___135\", \"ga_left_comm___Xx___142\",
     \"ga_comm_min_141\", \"ga_comm_max_140\", \"ga_assoc_min_149\",
     \"ga_assoc_max_147\", \"ga_left_comm_min_148\",
     \"ga_left_comm_max_146\", \"leq_def_Rat\", \"geq_def_Rat\",
     \"less_def_Rat\", \"greater_def_Rat\", \"minus_def_Rat\",
     \"abs_def_Rat\", \"add_def_Rat\", \"sub_def_Rat\",
     \"mult_def_Rat\", \"min_def_Rat\", \"max_def_Rat\",
     \"divide_def1_Rat\", \"divide_def2_Rat\", \"power_0_Rat\",
     \"power_suc_Rat\", \"power_neg_Rat\", \"distr1_Rat\",
     \"distr2_Rat\", \"sub_rule_Rat\", \"divide_dom_Rat\",
     \"divide_rule_Rat\", \"power_Rat\", \"AbsSignumLaw\", \"IPN01\",
     \"IPN02\", \"IPN03\", \"IPN04\", \"IPN05\", \"IPN06\", \"IPN07\",
     \"INN01\", \"INN02\", \"INN03\", \"INN04\", \"INN05\", \"INN06\",
     \"INN07\", \"IIN01\", \"IIN02\", \"IIN03\", \"IIN04\", \"IIN05\",
     \"IIN06\", \"IIN07\", \"IIN07_1\", \"IIN08\", \"IIN09\", \"IRN01\",
     \"IRN02\", \"IRN03\", \"IRN04\", \"IRN05\", \"IRN06\", \"IRN07\",
     \"IRN07_2\", \"IRN08\", \"IRN09\", \"IRI01\", \"IRI02\", \"IRI03\",
     \"IRI04\", \"IRI05\", \"IRI06\", \"IRI01_3\", \"IRI02_4\",
     \"IRF01\", \"IRF02\", \"ICE01\", \"ICE02\", \"ICO04\", \"ICO05\",
     \"ICO06\", \"ICO07\", \"ICO01\", \"ICO02\", \"ICO03\", \"ICO08\",
     \"ICO09\", \"ICO10\", \"ICO11\", \"StringT1\", \"StringT2\",
     \"StringT3\", \"StringT4\", \"StringT5\"]"

typedecl Bool
typedecl Char
typedecl ('a1) DList
typedecl ('a1) List
typedecl Pos
typedecl Rat
typedecl String
typedecl Unit
typedecl X_Int

datatype Ordering = EQ | GT | LT
datatype X_Nat = X0X2 ("0''''") |
                 sucX1 "X_Nat" ("suc''/'(_')" [3] 999)

consts
ACK :: "Char"
BEL :: "Char"
BS :: "Char"
CAN :: "Char"
CR :: "Char"
DC1 :: "Char"
DC2 :: "Char"
DC3 :: "Char"
DC4 :: "Char"
DEL :: "Char"
DLE :: "Char"
EM :: "Char"
ENQ :: "Char"
EOT :: "Char"
ESC :: "Char"
ETB :: "Char"
ETXX :: "Char" ("ETX")
FF :: "Char"
FS :: "Char"
GS :: "Char"
HT :: "Char"
LF :: "Char"
NAK :: "Char"
NL :: "Char"
NP :: "Char"
NUL :: "Char"
notH__X :: "bool => bool" ("(notH/ _)" [56] 56)
RS :: "Char"
SI :: "Char"
SO :: "Char"
SOH :: "Char"
SP :: "Char"
SUB :: "Char"
SYN :: "Char"
SYXX :: "Char" ("SYX")
US :: "Char"
VT :: "Char"
X'0' :: "Char" ("''0''")
X'1' :: "Char" ("''1''")
X'2' :: "Char" ("''2''")
X'3' :: "Char" ("''3''")
X'4' :: "Char" ("''4''")
X'5' :: "Char" ("''5''")
X'6' :: "Char" ("''6''")
X'7' :: "Char" ("''7''")
X'8' :: "Char" ("''8''")
X'9' :: "Char" ("''9''")
X'A' :: "Char" ("''A''")
X'B' :: "Char" ("''B''")
X'C' :: "Char" ("''C''")
X'D' :: "Char" ("''D''")
X'E' :: "Char" ("''E''")
X'F' :: "Char" ("''F''")
X'G' :: "Char" ("''G''")
X'H' :: "Char" ("''H''")
X'I' :: "Char" ("''I''")
X'J' :: "Char" ("''J''")
X'K' :: "Char" ("''K''")
X'L' :: "Char" ("''L''")
X'M' :: "Char" ("''M''")
X'N' :: "Char" ("''N''")
X'O' :: "Char" ("''O''")
X'P' :: "Char" ("''P''")
X'Q' :: "Char" ("''Q''")
X'R' :: "Char" ("''R''")
X'S' :: "Char" ("''S''")
X'T' :: "Char" ("''T''")
X'U' :: "Char" ("''U''")
X'V' :: "Char" ("''V''")
X'W' :: "Char" ("''W''")
X'XAElig' :: "Char" ("''Æ''")
X'XAacute' :: "Char" ("''Á''")
X'XAcirc' :: "Char" ("''Â''")
X'XAgrave' :: "Char" ("''À''")
X'XAmp' :: "Char" ("''&''")
X'XAring' :: "Char" ("''Å''")
X'XAt' :: "Char" ("''@''")
X'XAtilde' :: "Char" ("''Ã''")
X'XAuml' :: "Char" ("''Ä''")
X'XBslash'' :: "Char" ("''\\''''")
X'XBslash000' :: "Char" ("''\\000''")
X'XBslash001' :: "Char" ("''\\001''")
X'XBslash002' :: "Char" ("''\\002''")
X'XBslash003' :: "Char" ("''\\003''")
X'XBslash004' :: "Char" ("''\\004''")
X'XBslash005' :: "Char" ("''\\005''")
X'XBslash006' :: "Char" ("''\\006''")
X'XBslash007' :: "Char" ("''\\007''")
X'XBslash008' :: "Char" ("''\\008''")
X'XBslash009' :: "Char" ("''\\009''")
X'XBslash010' :: "Char" ("''\\010''")
X'XBslash011' :: "Char" ("''\\011''")
X'XBslash012' :: "Char" ("''\\012''")
X'XBslash013' :: "Char" ("''\\013''")
X'XBslash014' :: "Char" ("''\\014''")
X'XBslash015' :: "Char" ("''\\015''")
X'XBslash016' :: "Char" ("''\\016''")
X'XBslash017' :: "Char" ("''\\017''")
X'XBslash018' :: "Char" ("''\\018''")
X'XBslash019' :: "Char" ("''\\019''")
X'XBslash020' :: "Char" ("''\\020''")
X'XBslash021' :: "Char" ("''\\021''")
X'XBslash022' :: "Char" ("''\\022''")
X'XBslash023' :: "Char" ("''\\023''")
X'XBslash024' :: "Char" ("''\\024''")
X'XBslash025' :: "Char" ("''\\025''")
X'XBslash026' :: "Char" ("''\\026''")
X'XBslash027' :: "Char" ("''\\027''")
X'XBslash028' :: "Char" ("''\\028''")
X'XBslash029' :: "Char" ("''\\029''")
X'XBslash030' :: "Char" ("''\\030''")
X'XBslash031' :: "Char" ("''\\031''")
X'XBslash032' :: "Char" ("''\\032''")
X'XBslash033' :: "Char" ("''\\033''")
X'XBslash034' :: "Char" ("''\\034''")
X'XBslash035' :: "Char" ("''\\035''")
X'XBslash036' :: "Char" ("''\\036''")
X'XBslash037' :: "Char" ("''\\037''")
X'XBslash038' :: "Char" ("''\\038''")
X'XBslash039' :: "Char" ("''\\039''")
X'XBslash040' :: "Char" ("''\\040''")
X'XBslash041' :: "Char" ("''\\041''")
X'XBslash042' :: "Char" ("''\\042''")
X'XBslash043' :: "Char" ("''\\043''")
X'XBslash044' :: "Char" ("''\\044''")
X'XBslash045' :: "Char" ("''\\045''")
X'XBslash046' :: "Char" ("''\\046''")
X'XBslash047' :: "Char" ("''\\047''")
X'XBslash048' :: "Char" ("''\\048''")
X'XBslash049' :: "Char" ("''\\049''")
X'XBslash050' :: "Char" ("''\\050''")
X'XBslash051' :: "Char" ("''\\051''")
X'XBslash052' :: "Char" ("''\\052''")
X'XBslash053' :: "Char" ("''\\053''")
X'XBslash054' :: "Char" ("''\\054''")
X'XBslash055' :: "Char" ("''\\055''")
X'XBslash056' :: "Char" ("''\\056''")
X'XBslash057' :: "Char" ("''\\057''")
X'XBslash058' :: "Char" ("''\\058''")
X'XBslash059' :: "Char" ("''\\059''")
X'XBslash060' :: "Char" ("''\\060''")
X'XBslash061' :: "Char" ("''\\061''")
X'XBslash062' :: "Char" ("''\\062''")
X'XBslash063' :: "Char" ("''\\063''")
X'XBslash064' :: "Char" ("''\\064''")
X'XBslash065' :: "Char" ("''\\065''")
X'XBslash066' :: "Char" ("''\\066''")
X'XBslash067' :: "Char" ("''\\067''")
X'XBslash068' :: "Char" ("''\\068''")
X'XBslash069' :: "Char" ("''\\069''")
X'XBslash070' :: "Char" ("''\\070''")
X'XBslash071' :: "Char" ("''\\071''")
X'XBslash072' :: "Char" ("''\\072''")
X'XBslash073' :: "Char" ("''\\073''")
X'XBslash074' :: "Char" ("''\\074''")
X'XBslash075' :: "Char" ("''\\075''")
X'XBslash076' :: "Char" ("''\\076''")
X'XBslash077' :: "Char" ("''\\077''")
X'XBslash078' :: "Char" ("''\\078''")
X'XBslash079' :: "Char" ("''\\079''")
X'XBslash080' :: "Char" ("''\\080''")
X'XBslash081' :: "Char" ("''\\081''")
X'XBslash082' :: "Char" ("''\\082''")
X'XBslash083' :: "Char" ("''\\083''")
X'XBslash084' :: "Char" ("''\\084''")
X'XBslash085' :: "Char" ("''\\085''")
X'XBslash086' :: "Char" ("''\\086''")
X'XBslash087' :: "Char" ("''\\087''")
X'XBslash088' :: "Char" ("''\\088''")
X'XBslash089' :: "Char" ("''\\089''")
X'XBslash090' :: "Char" ("''\\090''")
X'XBslash091' :: "Char" ("''\\091''")
X'XBslash092' :: "Char" ("''\\092''")
X'XBslash093' :: "Char" ("''\\093''")
X'XBslash094' :: "Char" ("''\\094''")
X'XBslash095' :: "Char" ("''\\095''")
X'XBslash096' :: "Char" ("''\\096''")
X'XBslash097' :: "Char" ("''\\097''")
X'XBslash098' :: "Char" ("''\\098''")
X'XBslash099' :: "Char" ("''\\099''")
X'XBslash100' :: "Char" ("''\\100''")
X'XBslash101' :: "Char" ("''\\101''")
X'XBslash102' :: "Char" ("''\\102''")
X'XBslash103' :: "Char" ("''\\103''")
X'XBslash104' :: "Char" ("''\\104''")
X'XBslash105' :: "Char" ("''\\105''")
X'XBslash106' :: "Char" ("''\\106''")
X'XBslash107' :: "Char" ("''\\107''")
X'XBslash108' :: "Char" ("''\\108''")
X'XBslash109' :: "Char" ("''\\109''")
X'XBslash110' :: "Char" ("''\\110''")
X'XBslash111' :: "Char" ("''\\111''")
X'XBslash112' :: "Char" ("''\\112''")
X'XBslash113' :: "Char" ("''\\113''")
X'XBslash114' :: "Char" ("''\\114''")
X'XBslash115' :: "Char" ("''\\115''")
X'XBslash116' :: "Char" ("''\\116''")
X'XBslash117' :: "Char" ("''\\117''")
X'XBslash118' :: "Char" ("''\\118''")
X'XBslash119' :: "Char" ("''\\119''")
X'XBslash120' :: "Char" ("''\\120''")
X'XBslash121' :: "Char" ("''\\121''")
X'XBslash122' :: "Char" ("''\\122''")
X'XBslash123' :: "Char" ("''\\123''")
X'XBslash124' :: "Char" ("''\\124''")
X'XBslash125' :: "Char" ("''\\125''")
X'XBslash126' :: "Char" ("''\\126''")
X'XBslash127' :: "Char" ("''\\127''")
X'XBslash128' :: "Char" ("''\\128''")
X'XBslash129' :: "Char" ("''\\129''")
X'XBslash130' :: "Char" ("''\\130''")
X'XBslash131' :: "Char" ("''\\131''")
X'XBslash132' :: "Char" ("''\\132''")
X'XBslash133' :: "Char" ("''\\133''")
X'XBslash134' :: "Char" ("''\\134''")
X'XBslash135' :: "Char" ("''\\135''")
X'XBslash136' :: "Char" ("''\\136''")
X'XBslash137' :: "Char" ("''\\137''")
X'XBslash138' :: "Char" ("''\\138''")
X'XBslash139' :: "Char" ("''\\139''")
X'XBslash140' :: "Char" ("''\\140''")
X'XBslash141' :: "Char" ("''\\141''")
X'XBslash142' :: "Char" ("''\\142''")
X'XBslash143' :: "Char" ("''\\143''")
X'XBslash144' :: "Char" ("''\\144''")
X'XBslash145' :: "Char" ("''\\145''")
X'XBslash146' :: "Char" ("''\\146''")
X'XBslash147' :: "Char" ("''\\147''")
X'XBslash148' :: "Char" ("''\\148''")
X'XBslash149' :: "Char" ("''\\149''")
X'XBslash150' :: "Char" ("''\\150''")
X'XBslash151' :: "Char" ("''\\151''")
X'XBslash152' :: "Char" ("''\\152''")
X'XBslash153' :: "Char" ("''\\153''")
X'XBslash154' :: "Char" ("''\\154''")
X'XBslash155' :: "Char" ("''\\155''")
X'XBslash156' :: "Char" ("''\\156''")
X'XBslash157' :: "Char" ("''\\157''")
X'XBslash158' :: "Char" ("''\\158''")
X'XBslash159' :: "Char" ("''\\159''")
X'XBslash160' :: "Char" ("''\\160''")
X'XBslash161' :: "Char" ("''\\161''")
X'XBslash162' :: "Char" ("''\\162''")
X'XBslash163' :: "Char" ("''\\163''")
X'XBslash164' :: "Char" ("''\\164''")
X'XBslash165' :: "Char" ("''\\165''")
X'XBslash166' :: "Char" ("''\\166''")
X'XBslash167' :: "Char" ("''\\167''")
X'XBslash168' :: "Char" ("''\\168''")
X'XBslash169' :: "Char" ("''\\169''")
X'XBslash170' :: "Char" ("''\\170''")
X'XBslash171' :: "Char" ("''\\171''")
X'XBslash172' :: "Char" ("''\\172''")
X'XBslash173' :: "Char" ("''\\173''")
X'XBslash174' :: "Char" ("''\\174''")
X'XBslash175' :: "Char" ("''\\175''")
X'XBslash176' :: "Char" ("''\\176''")
X'XBslash177' :: "Char" ("''\\177''")
X'XBslash178' :: "Char" ("''\\178''")
X'XBslash179' :: "Char" ("''\\179''")
X'XBslash180' :: "Char" ("''\\180''")
X'XBslash181' :: "Char" ("''\\181''")
X'XBslash182' :: "Char" ("''\\182''")
X'XBslash183' :: "Char" ("''\\183''")
X'XBslash184' :: "Char" ("''\\184''")
X'XBslash185' :: "Char" ("''\\185''")
X'XBslash186' :: "Char" ("''\\186''")
X'XBslash187' :: "Char" ("''\\187''")
X'XBslash188' :: "Char" ("''\\188''")
X'XBslash189' :: "Char" ("''\\189''")
X'XBslash190' :: "Char" ("''\\190''")
X'XBslash191' :: "Char" ("''\\191''")
X'XBslash192' :: "Char" ("''\\192''")
X'XBslash193' :: "Char" ("''\\193''")
X'XBslash194' :: "Char" ("''\\194''")
X'XBslash195' :: "Char" ("''\\195''")
X'XBslash196' :: "Char" ("''\\196''")
X'XBslash197' :: "Char" ("''\\197''")
X'XBslash198' :: "Char" ("''\\198''")
X'XBslash199' :: "Char" ("''\\199''")
X'XBslash200' :: "Char" ("''\\200''")
X'XBslash201' :: "Char" ("''\\201''")
X'XBslash202' :: "Char" ("''\\202''")
X'XBslash203' :: "Char" ("''\\203''")
X'XBslash204' :: "Char" ("''\\204''")
X'XBslash205' :: "Char" ("''\\205''")
X'XBslash206' :: "Char" ("''\\206''")
X'XBslash207' :: "Char" ("''\\207''")
X'XBslash208' :: "Char" ("''\\208''")
X'XBslash209' :: "Char" ("''\\209''")
X'XBslash210' :: "Char" ("''\\210''")
X'XBslash211' :: "Char" ("''\\211''")
X'XBslash212' :: "Char" ("''\\212''")
X'XBslash213' :: "Char" ("''\\213''")
X'XBslash214' :: "Char" ("''\\214''")
X'XBslash215' :: "Char" ("''\\215''")
X'XBslash216' :: "Char" ("''\\216''")
X'XBslash217' :: "Char" ("''\\217''")
X'XBslash218' :: "Char" ("''\\218''")
X'XBslash219' :: "Char" ("''\\219''")
X'XBslash220' :: "Char" ("''\\220''")
X'XBslash221' :: "Char" ("''\\221''")
X'XBslash222' :: "Char" ("''\\222''")
X'XBslash223' :: "Char" ("''\\223''")
X'XBslash224' :: "Char" ("''\\224''")
X'XBslash225' :: "Char" ("''\\225''")
X'XBslash226' :: "Char" ("''\\226''")
X'XBslash227' :: "Char" ("''\\227''")
X'XBslash228' :: "Char" ("''\\228''")
X'XBslash229' :: "Char" ("''\\229''")
X'XBslash230' :: "Char" ("''\\230''")
X'XBslash231' :: "Char" ("''\\231''")
X'XBslash232' :: "Char" ("''\\232''")
X'XBslash233' :: "Char" ("''\\233''")
X'XBslash234' :: "Char" ("''\\234''")
X'XBslash235' :: "Char" ("''\\235''")
X'XBslash236' :: "Char" ("''\\236''")
X'XBslash237' :: "Char" ("''\\237''")
X'XBslash238' :: "Char" ("''\\238''")
X'XBslash239' :: "Char" ("''\\239''")
X'XBslash240' :: "Char" ("''\\240''")
X'XBslash241' :: "Char" ("''\\241''")
X'XBslash242' :: "Char" ("''\\242''")
X'XBslash243' :: "Char" ("''\\243''")
X'XBslash244' :: "Char" ("''\\244''")
X'XBslash245' :: "Char" ("''\\245''")
X'XBslash246' :: "Char" ("''\\246''")
X'XBslash247' :: "Char" ("''\\247''")
X'XBslash248' :: "Char" ("''\\248''")
X'XBslash249' :: "Char" ("''\\249''")
X'XBslash250' :: "Char" ("''\\250''")
X'XBslash251' :: "Char" ("''\\251''")
X'XBslash252' :: "Char" ("''\\252''")
X'XBslash253' :: "Char" ("''\\253''")
X'XBslash254' :: "Char" ("''\\254''")
X'XBslash255' :: "Char" ("''\\255''")
X'XBslashXBslash' :: "Char" ("''\\\\''")
X'XBslashXQuest' :: "Char" ("''\\?''")
X'XBslashXQuot' :: "Char" ("''\\\"''")
X'XBslasha' :: "Char" ("''\\a''")
X'XBslashb' :: "Char" ("''\\b''")
X'XBslashf' :: "Char" ("''\\f''")
X'XBslashn' :: "Char" ("''\\n''")
X'XBslasho000' :: "Char" ("''\\o000''")
X'XBslasho001' :: "Char" ("''\\o001''")
X'XBslasho002' :: "Char" ("''\\o002''")
X'XBslasho003' :: "Char" ("''\\o003''")
X'XBslasho004' :: "Char" ("''\\o004''")
X'XBslasho005' :: "Char" ("''\\o005''")
X'XBslasho006' :: "Char" ("''\\o006''")
X'XBslasho007' :: "Char" ("''\\o007''")
X'XBslasho010' :: "Char" ("''\\o010''")
X'XBslasho011' :: "Char" ("''\\o011''")
X'XBslasho012' :: "Char" ("''\\o012''")
X'XBslasho013' :: "Char" ("''\\o013''")
X'XBslasho014' :: "Char" ("''\\o014''")
X'XBslasho015' :: "Char" ("''\\o015''")
X'XBslasho016' :: "Char" ("''\\o016''")
X'XBslasho017' :: "Char" ("''\\o017''")
X'XBslasho020' :: "Char" ("''\\o020''")
X'XBslasho021' :: "Char" ("''\\o021''")
X'XBslasho022' :: "Char" ("''\\o022''")
X'XBslasho023' :: "Char" ("''\\o023''")
X'XBslasho024' :: "Char" ("''\\o024''")
X'XBslasho025' :: "Char" ("''\\o025''")
X'XBslasho026' :: "Char" ("''\\o026''")
X'XBslasho027' :: "Char" ("''\\o027''")
X'XBslasho030' :: "Char" ("''\\o030''")
X'XBslasho031' :: "Char" ("''\\o031''")
X'XBslasho032' :: "Char" ("''\\o032''")
X'XBslasho033' :: "Char" ("''\\o033''")
X'XBslasho034' :: "Char" ("''\\o034''")
X'XBslasho035' :: "Char" ("''\\o035''")
X'XBslasho036' :: "Char" ("''\\o036''")
X'XBslasho037' :: "Char" ("''\\o037''")
X'XBslasho040' :: "Char" ("''\\o040''")
X'XBslasho041' :: "Char" ("''\\o041''")
X'XBslasho042' :: "Char" ("''\\o042''")
X'XBslasho043' :: "Char" ("''\\o043''")
X'XBslasho044' :: "Char" ("''\\o044''")
X'XBslasho045' :: "Char" ("''\\o045''")
X'XBslasho046' :: "Char" ("''\\o046''")
X'XBslasho047' :: "Char" ("''\\o047''")
X'XBslasho050' :: "Char" ("''\\o050''")
X'XBslasho051' :: "Char" ("''\\o051''")
X'XBslasho052' :: "Char" ("''\\o052''")
X'XBslasho053' :: "Char" ("''\\o053''")
X'XBslasho054' :: "Char" ("''\\o054''")
X'XBslasho055' :: "Char" ("''\\o055''")
X'XBslasho056' :: "Char" ("''\\o056''")
X'XBslasho057' :: "Char" ("''\\o057''")
X'XBslasho060' :: "Char" ("''\\o060''")
X'XBslasho061' :: "Char" ("''\\o061''")
X'XBslasho062' :: "Char" ("''\\o062''")
X'XBslasho063' :: "Char" ("''\\o063''")
X'XBslasho064' :: "Char" ("''\\o064''")
X'XBslasho065' :: "Char" ("''\\o065''")
X'XBslasho066' :: "Char" ("''\\o066''")
X'XBslasho067' :: "Char" ("''\\o067''")
X'XBslasho070' :: "Char" ("''\\o070''")
X'XBslasho071' :: "Char" ("''\\o071''")
X'XBslasho072' :: "Char" ("''\\o072''")
X'XBslasho073' :: "Char" ("''\\o073''")
X'XBslasho074' :: "Char" ("''\\o074''")
X'XBslasho075' :: "Char" ("''\\o075''")
X'XBslasho076' :: "Char" ("''\\o076''")
X'XBslasho077' :: "Char" ("''\\o077''")
X'XBslasho100' :: "Char" ("''\\o100''")
X'XBslasho101' :: "Char" ("''\\o101''")
X'XBslasho102' :: "Char" ("''\\o102''")
X'XBslasho103' :: "Char" ("''\\o103''")
X'XBslasho104' :: "Char" ("''\\o104''")
X'XBslasho105' :: "Char" ("''\\o105''")
X'XBslasho106' :: "Char" ("''\\o106''")
X'XBslasho107' :: "Char" ("''\\o107''")
X'XBslasho110' :: "Char" ("''\\o110''")
X'XBslasho111' :: "Char" ("''\\o111''")
X'XBslasho112' :: "Char" ("''\\o112''")
X'XBslasho113' :: "Char" ("''\\o113''")
X'XBslasho114' :: "Char" ("''\\o114''")
X'XBslasho115' :: "Char" ("''\\o115''")
X'XBslasho116' :: "Char" ("''\\o116''")
X'XBslasho117' :: "Char" ("''\\o117''")
X'XBslasho120' :: "Char" ("''\\o120''")
X'XBslasho121' :: "Char" ("''\\o121''")
X'XBslasho122' :: "Char" ("''\\o122''")
X'XBslasho123' :: "Char" ("''\\o123''")
X'XBslasho124' :: "Char" ("''\\o124''")
X'XBslasho125' :: "Char" ("''\\o125''")
X'XBslasho126' :: "Char" ("''\\o126''")
X'XBslasho127' :: "Char" ("''\\o127''")
X'XBslasho130' :: "Char" ("''\\o130''")
X'XBslasho131' :: "Char" ("''\\o131''")
X'XBslasho132' :: "Char" ("''\\o132''")
X'XBslasho133' :: "Char" ("''\\o133''")
X'XBslasho134' :: "Char" ("''\\o134''")
X'XBslasho135' :: "Char" ("''\\o135''")
X'XBslasho136' :: "Char" ("''\\o136''")
X'XBslasho137' :: "Char" ("''\\o137''")
X'XBslasho140' :: "Char" ("''\\o140''")
X'XBslasho141' :: "Char" ("''\\o141''")
X'XBslasho142' :: "Char" ("''\\o142''")
X'XBslasho143' :: "Char" ("''\\o143''")
X'XBslasho144' :: "Char" ("''\\o144''")
X'XBslasho145' :: "Char" ("''\\o145''")
X'XBslasho146' :: "Char" ("''\\o146''")
X'XBslasho147' :: "Char" ("''\\o147''")
X'XBslasho150' :: "Char" ("''\\o150''")
X'XBslasho151' :: "Char" ("''\\o151''")
X'XBslasho152' :: "Char" ("''\\o152''")
X'XBslasho153' :: "Char" ("''\\o153''")
X'XBslasho154' :: "Char" ("''\\o154''")
X'XBslasho155' :: "Char" ("''\\o155''")
X'XBslasho156' :: "Char" ("''\\o156''")
X'XBslasho157' :: "Char" ("''\\o157''")
X'XBslasho160' :: "Char" ("''\\o160''")
X'XBslasho161' :: "Char" ("''\\o161''")
X'XBslasho162' :: "Char" ("''\\o162''")
X'XBslasho163' :: "Char" ("''\\o163''")
X'XBslasho164' :: "Char" ("''\\o164''")
X'XBslasho165' :: "Char" ("''\\o165''")
X'XBslasho166' :: "Char" ("''\\o166''")
X'XBslasho167' :: "Char" ("''\\o167''")
X'XBslasho170' :: "Char" ("''\\o170''")
X'XBslasho171' :: "Char" ("''\\o171''")
X'XBslasho172' :: "Char" ("''\\o172''")
X'XBslasho173' :: "Char" ("''\\o173''")
X'XBslasho174' :: "Char" ("''\\o174''")
X'XBslasho175' :: "Char" ("''\\o175''")
X'XBslasho176' :: "Char" ("''\\o176''")
X'XBslasho177' :: "Char" ("''\\o177''")
X'XBslasho200' :: "Char" ("''\\o200''")
X'XBslasho201' :: "Char" ("''\\o201''")
X'XBslasho202' :: "Char" ("''\\o202''")
X'XBslasho203' :: "Char" ("''\\o203''")
X'XBslasho204' :: "Char" ("''\\o204''")
X'XBslasho205' :: "Char" ("''\\o205''")
X'XBslasho206' :: "Char" ("''\\o206''")
X'XBslasho207' :: "Char" ("''\\o207''")
X'XBslasho210' :: "Char" ("''\\o210''")
X'XBslasho211' :: "Char" ("''\\o211''")
X'XBslasho212' :: "Char" ("''\\o212''")
X'XBslasho213' :: "Char" ("''\\o213''")
X'XBslasho214' :: "Char" ("''\\o214''")
X'XBslasho215' :: "Char" ("''\\o215''")
X'XBslasho216' :: "Char" ("''\\o216''")
X'XBslasho217' :: "Char" ("''\\o217''")
X'XBslasho220' :: "Char" ("''\\o220''")
X'XBslasho221' :: "Char" ("''\\o221''")
X'XBslasho222' :: "Char" ("''\\o222''")
X'XBslasho223' :: "Char" ("''\\o223''")
X'XBslasho224' :: "Char" ("''\\o224''")
X'XBslasho225' :: "Char" ("''\\o225''")
X'XBslasho226' :: "Char" ("''\\o226''")
X'XBslasho227' :: "Char" ("''\\o227''")
X'XBslasho230' :: "Char" ("''\\o230''")
X'XBslasho231' :: "Char" ("''\\o231''")
X'XBslasho232' :: "Char" ("''\\o232''")
X'XBslasho233' :: "Char" ("''\\o233''")
X'XBslasho234' :: "Char" ("''\\o234''")
X'XBslasho235' :: "Char" ("''\\o235''")
X'XBslasho236' :: "Char" ("''\\o236''")
X'XBslasho237' :: "Char" ("''\\o237''")
X'XBslasho240' :: "Char" ("''\\o240''")
X'XBslasho241' :: "Char" ("''\\o241''")
X'XBslasho242' :: "Char" ("''\\o242''")
X'XBslasho243' :: "Char" ("''\\o243''")
X'XBslasho244' :: "Char" ("''\\o244''")
X'XBslasho245' :: "Char" ("''\\o245''")
X'XBslasho246' :: "Char" ("''\\o246''")
X'XBslasho247' :: "Char" ("''\\o247''")
X'XBslasho250' :: "Char" ("''\\o250''")
X'XBslasho251' :: "Char" ("''\\o251''")
X'XBslasho252' :: "Char" ("''\\o252''")
X'XBslasho253' :: "Char" ("''\\o253''")
X'XBslasho254' :: "Char" ("''\\o254''")
X'XBslasho255' :: "Char" ("''\\o255''")
X'XBslasho256' :: "Char" ("''\\o256''")
X'XBslasho257' :: "Char" ("''\\o257''")
X'XBslasho260' :: "Char" ("''\\o260''")
X'XBslasho261' :: "Char" ("''\\o261''")
X'XBslasho262' :: "Char" ("''\\o262''")
X'XBslasho263' :: "Char" ("''\\o263''")
X'XBslasho264' :: "Char" ("''\\o264''")
X'XBslasho265' :: "Char" ("''\\o265''")
X'XBslasho266' :: "Char" ("''\\o266''")
X'XBslasho267' :: "Char" ("''\\o267''")
X'XBslasho270' :: "Char" ("''\\o270''")
X'XBslasho271' :: "Char" ("''\\o271''")
X'XBslasho272' :: "Char" ("''\\o272''")
X'XBslasho273' :: "Char" ("''\\o273''")
X'XBslasho274' :: "Char" ("''\\o274''")
X'XBslasho275' :: "Char" ("''\\o275''")
X'XBslasho276' :: "Char" ("''\\o276''")
X'XBslasho277' :: "Char" ("''\\o277''")
X'XBslasho300' :: "Char" ("''\\o300''")
X'XBslasho301' :: "Char" ("''\\o301''")
X'XBslasho302' :: "Char" ("''\\o302''")
X'XBslasho303' :: "Char" ("''\\o303''")
X'XBslasho304' :: "Char" ("''\\o304''")
X'XBslasho305' :: "Char" ("''\\o305''")
X'XBslasho306' :: "Char" ("''\\o306''")
X'XBslasho307' :: "Char" ("''\\o307''")
X'XBslasho310' :: "Char" ("''\\o310''")
X'XBslasho311' :: "Char" ("''\\o311''")
X'XBslasho312' :: "Char" ("''\\o312''")
X'XBslasho313' :: "Char" ("''\\o313''")
X'XBslasho314' :: "Char" ("''\\o314''")
X'XBslasho315' :: "Char" ("''\\o315''")
X'XBslasho316' :: "Char" ("''\\o316''")
X'XBslasho317' :: "Char" ("''\\o317''")
X'XBslasho320' :: "Char" ("''\\o320''")
X'XBslasho321' :: "Char" ("''\\o321''")
X'XBslasho322' :: "Char" ("''\\o322''")
X'XBslasho323' :: "Char" ("''\\o323''")
X'XBslasho324' :: "Char" ("''\\o324''")
X'XBslasho325' :: "Char" ("''\\o325''")
X'XBslasho326' :: "Char" ("''\\o326''")
X'XBslasho327' :: "Char" ("''\\o327''")
X'XBslasho330' :: "Char" ("''\\o330''")
X'XBslasho331' :: "Char" ("''\\o331''")
X'XBslasho332' :: "Char" ("''\\o332''")
X'XBslasho333' :: "Char" ("''\\o333''")
X'XBslasho334' :: "Char" ("''\\o334''")
X'XBslasho335' :: "Char" ("''\\o335''")
X'XBslasho336' :: "Char" ("''\\o336''")
X'XBslasho337' :: "Char" ("''\\o337''")
X'XBslasho340' :: "Char" ("''\\o340''")
X'XBslasho341' :: "Char" ("''\\o341''")
X'XBslasho342' :: "Char" ("''\\o342''")
X'XBslasho343' :: "Char" ("''\\o343''")
X'XBslasho344' :: "Char" ("''\\o344''")
X'XBslasho345' :: "Char" ("''\\o345''")
X'XBslasho346' :: "Char" ("''\\o346''")
X'XBslasho347' :: "Char" ("''\\o347''")
X'XBslasho350' :: "Char" ("''\\o350''")
X'XBslasho351' :: "Char" ("''\\o351''")
X'XBslasho352' :: "Char" ("''\\o352''")
X'XBslasho353' :: "Char" ("''\\o353''")
X'XBslasho354' :: "Char" ("''\\o354''")
X'XBslasho355' :: "Char" ("''\\o355''")
X'XBslasho356' :: "Char" ("''\\o356''")
X'XBslasho357' :: "Char" ("''\\o357''")
X'XBslasho360' :: "Char" ("''\\o360''")
X'XBslasho361' :: "Char" ("''\\o361''")
X'XBslasho362' :: "Char" ("''\\o362''")
X'XBslasho363' :: "Char" ("''\\o363''")
X'XBslasho364' :: "Char" ("''\\o364''")
X'XBslasho365' :: "Char" ("''\\o365''")
X'XBslasho366' :: "Char" ("''\\o366''")
X'XBslasho367' :: "Char" ("''\\o367''")
X'XBslasho370' :: "Char" ("''\\o370''")
X'XBslasho371' :: "Char" ("''\\o371''")
X'XBslasho372' :: "Char" ("''\\o372''")
X'XBslasho373' :: "Char" ("''\\o373''")
X'XBslasho374' :: "Char" ("''\\o374''")
X'XBslasho375' :: "Char" ("''\\o375''")
X'XBslasho376' :: "Char" ("''\\o376''")
X'XBslasho377' :: "Char" ("''\\o377''")
X'XBslashr' :: "Char" ("''\\r''")
X'XBslasht' :: "Char" ("''\\t''")
X'XBslashv' :: "Char" ("''\\v''")
X'XBslashx00' :: "Char" ("''\\x00''")
X'XBslashx01' :: "Char" ("''\\x01''")
X'XBslashx02' :: "Char" ("''\\x02''")
X'XBslashx03' :: "Char" ("''\\x03''")
X'XBslashx04' :: "Char" ("''\\x04''")
X'XBslashx05' :: "Char" ("''\\x05''")
X'XBslashx06' :: "Char" ("''\\x06''")
X'XBslashx07' :: "Char" ("''\\x07''")
X'XBslashx08' :: "Char" ("''\\x08''")
X'XBslashx09' :: "Char" ("''\\x09''")
X'XBslashx0A' :: "Char" ("''\\x0A''")
X'XBslashx0B' :: "Char" ("''\\x0B''")
X'XBslashx0C' :: "Char" ("''\\x0C''")
X'XBslashx0D' :: "Char" ("''\\x0D''")
X'XBslashx0E' :: "Char" ("''\\x0E''")
X'XBslashx0F' :: "Char" ("''\\x0F''")
X'XBslashx10' :: "Char" ("''\\x10''")
X'XBslashx11' :: "Char" ("''\\x11''")
X'XBslashx12' :: "Char" ("''\\x12''")
X'XBslashx13' :: "Char" ("''\\x13''")
X'XBslashx14' :: "Char" ("''\\x14''")
X'XBslashx15' :: "Char" ("''\\x15''")
X'XBslashx16' :: "Char" ("''\\x16''")
X'XBslashx17' :: "Char" ("''\\x17''")
X'XBslashx18' :: "Char" ("''\\x18''")
X'XBslashx19' :: "Char" ("''\\x19''")
X'XBslashx1A' :: "Char" ("''\\x1A''")
X'XBslashx1B' :: "Char" ("''\\x1B''")
X'XBslashx1C' :: "Char" ("''\\x1C''")
X'XBslashx1D' :: "Char" ("''\\x1D''")
X'XBslashx1E' :: "Char" ("''\\x1E''")
X'XBslashx1F' :: "Char" ("''\\x1F''")
X'XBslashx20' :: "Char" ("''\\x20''")
X'XBslashx21' :: "Char" ("''\\x21''")
X'XBslashx22' :: "Char" ("''\\x22''")
X'XBslashx23' :: "Char" ("''\\x23''")
X'XBslashx24' :: "Char" ("''\\x24''")
X'XBslashx25' :: "Char" ("''\\x25''")
X'XBslashx26' :: "Char" ("''\\x26''")
X'XBslashx27' :: "Char" ("''\\x27''")
X'XBslashx28' :: "Char" ("''\\x28''")
X'XBslashx29' :: "Char" ("''\\x29''")
X'XBslashx2A' :: "Char" ("''\\x2A''")
X'XBslashx2B' :: "Char" ("''\\x2B''")
X'XBslashx2C' :: "Char" ("''\\x2C''")
X'XBslashx2D' :: "Char" ("''\\x2D''")
X'XBslashx2E' :: "Char" ("''\\x2E''")
X'XBslashx2F' :: "Char" ("''\\x2F''")
X'XBslashx30' :: "Char" ("''\\x30''")
X'XBslashx31' :: "Char" ("''\\x31''")
X'XBslashx32' :: "Char" ("''\\x32''")
X'XBslashx33' :: "Char" ("''\\x33''")
X'XBslashx34' :: "Char" ("''\\x34''")
X'XBslashx35' :: "Char" ("''\\x35''")
X'XBslashx36' :: "Char" ("''\\x36''")
X'XBslashx37' :: "Char" ("''\\x37''")
X'XBslashx38' :: "Char" ("''\\x38''")
X'XBslashx39' :: "Char" ("''\\x39''")
X'XBslashx3A' :: "Char" ("''\\x3A''")
X'XBslashx3B' :: "Char" ("''\\x3B''")
X'XBslashx3C' :: "Char" ("''\\x3C''")
X'XBslashx3D' :: "Char" ("''\\x3D''")
X'XBslashx3E' :: "Char" ("''\\x3E''")
X'XBslashx3F' :: "Char" ("''\\x3F''")
X'XBslashx40' :: "Char" ("''\\x40''")
X'XBslashx41' :: "Char" ("''\\x41''")
X'XBslashx42' :: "Char" ("''\\x42''")
X'XBslashx43' :: "Char" ("''\\x43''")
X'XBslashx44' :: "Char" ("''\\x44''")
X'XBslashx45' :: "Char" ("''\\x45''")
X'XBslashx46' :: "Char" ("''\\x46''")
X'XBslashx47' :: "Char" ("''\\x47''")
X'XBslashx48' :: "Char" ("''\\x48''")
X'XBslashx49' :: "Char" ("''\\x49''")
X'XBslashx4A' :: "Char" ("''\\x4A''")
X'XBslashx4B' :: "Char" ("''\\x4B''")
X'XBslashx4C' :: "Char" ("''\\x4C''")
X'XBslashx4D' :: "Char" ("''\\x4D''")
X'XBslashx4E' :: "Char" ("''\\x4E''")
X'XBslashx4F' :: "Char" ("''\\x4F''")
X'XBslashx50' :: "Char" ("''\\x50''")
X'XBslashx51' :: "Char" ("''\\x51''")
X'XBslashx52' :: "Char" ("''\\x52''")
X'XBslashx53' :: "Char" ("''\\x53''")
X'XBslashx54' :: "Char" ("''\\x54''")
X'XBslashx55' :: "Char" ("''\\x55''")
X'XBslashx56' :: "Char" ("''\\x56''")
X'XBslashx57' :: "Char" ("''\\x57''")
X'XBslashx58' :: "Char" ("''\\x58''")
X'XBslashx59' :: "Char" ("''\\x59''")
X'XBslashx5A' :: "Char" ("''\\x5A''")
X'XBslashx5B' :: "Char" ("''\\x5B''")
X'XBslashx5C' :: "Char" ("''\\x5C''")
X'XBslashx5D' :: "Char" ("''\\x5D''")
X'XBslashx5E' :: "Char" ("''\\x5E''")
X'XBslashx5F' :: "Char" ("''\\x5F''")
X'XBslashx60' :: "Char" ("''\\x60''")
X'XBslashx61' :: "Char" ("''\\x61''")
X'XBslashx62' :: "Char" ("''\\x62''")
X'XBslashx63' :: "Char" ("''\\x63''")
X'XBslashx64' :: "Char" ("''\\x64''")
X'XBslashx65' :: "Char" ("''\\x65''")
X'XBslashx66' :: "Char" ("''\\x66''")
X'XBslashx67' :: "Char" ("''\\x67''")
X'XBslashx68' :: "Char" ("''\\x68''")
X'XBslashx69' :: "Char" ("''\\x69''")
X'XBslashx6A' :: "Char" ("''\\x6A''")
X'XBslashx6B' :: "Char" ("''\\x6B''")
X'XBslashx6C' :: "Char" ("''\\x6C''")
X'XBslashx6D' :: "Char" ("''\\x6D''")
X'XBslashx6E' :: "Char" ("''\\x6E''")
X'XBslashx6F' :: "Char" ("''\\x6F''")
X'XBslashx70' :: "Char" ("''\\x70''")
X'XBslashx71' :: "Char" ("''\\x71''")
X'XBslashx72' :: "Char" ("''\\x72''")
X'XBslashx73' :: "Char" ("''\\x73''")
X'XBslashx74' :: "Char" ("''\\x74''")
X'XBslashx75' :: "Char" ("''\\x75''")
X'XBslashx76' :: "Char" ("''\\x76''")
X'XBslashx77' :: "Char" ("''\\x77''")
X'XBslashx78' :: "Char" ("''\\x78''")
X'XBslashx79' :: "Char" ("''\\x79''")
X'XBslashx7A' :: "Char" ("''\\x7A''")
X'XBslashx7B' :: "Char" ("''\\x7B''")
X'XBslashx7C' :: "Char" ("''\\x7C''")
X'XBslashx7D' :: "Char" ("''\\x7D''")
X'XBslashx7E' :: "Char" ("''\\x7E''")
X'XBslashx7F' :: "Char" ("''\\x7F''")
X'XBslashx80' :: "Char" ("''\\x80''")
X'XBslashx81' :: "Char" ("''\\x81''")
X'XBslashx82' :: "Char" ("''\\x82''")
X'XBslashx83' :: "Char" ("''\\x83''")
X'XBslashx84' :: "Char" ("''\\x84''")
X'XBslashx85' :: "Char" ("''\\x85''")
X'XBslashx86' :: "Char" ("''\\x86''")
X'XBslashx87' :: "Char" ("''\\x87''")
X'XBslashx88' :: "Char" ("''\\x88''")
X'XBslashx89' :: "Char" ("''\\x89''")
X'XBslashx8A' :: "Char" ("''\\x8A''")
X'XBslashx8B' :: "Char" ("''\\x8B''")
X'XBslashx8C' :: "Char" ("''\\x8C''")
X'XBslashx8D' :: "Char" ("''\\x8D''")
X'XBslashx8E' :: "Char" ("''\\x8E''")
X'XBslashx8F' :: "Char" ("''\\x8F''")
X'XBslashx90' :: "Char" ("''\\x90''")
X'XBslashx91' :: "Char" ("''\\x91''")
X'XBslashx92' :: "Char" ("''\\x92''")
X'XBslashx93' :: "Char" ("''\\x93''")
X'XBslashx94' :: "Char" ("''\\x94''")
X'XBslashx95' :: "Char" ("''\\x95''")
X'XBslashx96' :: "Char" ("''\\x96''")
X'XBslashx97' :: "Char" ("''\\x97''")
X'XBslashx98' :: "Char" ("''\\x98''")
X'XBslashx99' :: "Char" ("''\\x99''")
X'XBslashx9A' :: "Char" ("''\\x9A''")
X'XBslashx9B' :: "Char" ("''\\x9B''")
X'XBslashx9C' :: "Char" ("''\\x9C''")
X'XBslashx9D' :: "Char" ("''\\x9D''")
X'XBslashx9E' :: "Char" ("''\\x9E''")
X'XBslashx9F' :: "Char" ("''\\x9F''")
X'XBslashxA0' :: "Char" ("''\\xA0''")
X'XBslashxA1' :: "Char" ("''\\xA1''")
X'XBslashxA2' :: "Char" ("''\\xA2''")
X'XBslashxA3' :: "Char" ("''\\xA3''")
X'XBslashxA4' :: "Char" ("''\\xA4''")
X'XBslashxA5' :: "Char" ("''\\xA5''")
X'XBslashxA6' :: "Char" ("''\\xA6''")
X'XBslashxA7' :: "Char" ("''\\xA7''")
X'XBslashxA8' :: "Char" ("''\\xA8''")
X'XBslashxA9' :: "Char" ("''\\xA9''")
X'XBslashxAA' :: "Char" ("''\\xAA''")
X'XBslashxAB' :: "Char" ("''\\xAB''")
X'XBslashxAC' :: "Char" ("''\\xAC''")
X'XBslashxAD' :: "Char" ("''\\xAD''")
X'XBslashxAE' :: "Char" ("''\\xAE''")
X'XBslashxAF' :: "Char" ("''\\xAF''")
X'XBslashxB0' :: "Char" ("''\\xB0''")
X'XBslashxB1' :: "Char" ("''\\xB1''")
X'XBslashxB2' :: "Char" ("''\\xB2''")
X'XBslashxB3' :: "Char" ("''\\xB3''")
X'XBslashxB4' :: "Char" ("''\\xB4''")
X'XBslashxB5' :: "Char" ("''\\xB5''")
X'XBslashxB6' :: "Char" ("''\\xB6''")
X'XBslashxB7' :: "Char" ("''\\xB7''")
X'XBslashxB8' :: "Char" ("''\\xB8''")
X'XBslashxB9' :: "Char" ("''\\xB9''")
X'XBslashxBA' :: "Char" ("''\\xBA''")
X'XBslashxBB' :: "Char" ("''\\xBB''")
X'XBslashxBC' :: "Char" ("''\\xBC''")
X'XBslashxBD' :: "Char" ("''\\xBD''")
X'XBslashxBE' :: "Char" ("''\\xBE''")
X'XBslashxBF' :: "Char" ("''\\xBF''")
X'XBslashxC0' :: "Char" ("''\\xC0''")
X'XBslashxC1' :: "Char" ("''\\xC1''")
X'XBslashxC2' :: "Char" ("''\\xC2''")
X'XBslashxC3' :: "Char" ("''\\xC3''")
X'XBslashxC4' :: "Char" ("''\\xC4''")
X'XBslashxC5' :: "Char" ("''\\xC5''")
X'XBslashxC6' :: "Char" ("''\\xC6''")
X'XBslashxC7' :: "Char" ("''\\xC7''")
X'XBslashxC8' :: "Char" ("''\\xC8''")
X'XBslashxC9' :: "Char" ("''\\xC9''")
X'XBslashxCA' :: "Char" ("''\\xCA''")
X'XBslashxCB' :: "Char" ("''\\xCB''")
X'XBslashxCC' :: "Char" ("''\\xCC''")
X'XBslashxCD' :: "Char" ("''\\xCD''")
X'XBslashxCE' :: "Char" ("''\\xCE''")
X'XBslashxCF' :: "Char" ("''\\xCF''")
X'XBslashxD0' :: "Char" ("''\\xD0''")
X'XBslashxD1' :: "Char" ("''\\xD1''")
X'XBslashxD2' :: "Char" ("''\\xD2''")
X'XBslashxD3' :: "Char" ("''\\xD3''")
X'XBslashxD4' :: "Char" ("''\\xD4''")
X'XBslashxD5' :: "Char" ("''\\xD5''")
X'XBslashxD6' :: "Char" ("''\\xD6''")
X'XBslashxD7' :: "Char" ("''\\xD7''")
X'XBslashxD8' :: "Char" ("''\\xD8''")
X'XBslashxD9' :: "Char" ("''\\xD9''")
X'XBslashxDA' :: "Char" ("''\\xDA''")
X'XBslashxDB' :: "Char" ("''\\xDB''")
X'XBslashxDC' :: "Char" ("''\\xDC''")
X'XBslashxDD' :: "Char" ("''\\xDD''")
X'XBslashxDE' :: "Char" ("''\\xDE''")
X'XBslashxDF' :: "Char" ("''\\xDF''")
X'XBslashxE0' :: "Char" ("''\\xE0''")
X'XBslashxE1' :: "Char" ("''\\xE1''")
X'XBslashxE2' :: "Char" ("''\\xE2''")
X'XBslashxE3' :: "Char" ("''\\xE3''")
X'XBslashxE4' :: "Char" ("''\\xE4''")
X'XBslashxE5' :: "Char" ("''\\xE5''")
X'XBslashxE6' :: "Char" ("''\\xE6''")
X'XBslashxE7' :: "Char" ("''\\xE7''")
X'XBslashxE8' :: "Char" ("''\\xE8''")
X'XBslashxE9' :: "Char" ("''\\xE9''")
X'XBslashxEA' :: "Char" ("''\\xEA''")
X'XBslashxEB' :: "Char" ("''\\xEB''")
X'XBslashxEC' :: "Char" ("''\\xEC''")
X'XBslashxED' :: "Char" ("''\\xED''")
X'XBslashxEE' :: "Char" ("''\\xEE''")
X'XBslashxEF' :: "Char" ("''\\xEF''")
X'XBslashxF0' :: "Char" ("''\\xF0''")
X'XBslashxF1' :: "Char" ("''\\xF1''")
X'XBslashxF2' :: "Char" ("''\\xF2''")
X'XBslashxF3' :: "Char" ("''\\xF3''")
X'XBslashxF4' :: "Char" ("''\\xF4''")
X'XBslashxF5' :: "Char" ("''\\xF5''")
X'XBslashxF6' :: "Char" ("''\\xF6''")
X'XBslashxF7' :: "Char" ("''\\xF7''")
X'XBslashxF8' :: "Char" ("''\\xF8''")
X'XBslashxF9' :: "Char" ("''\\xF9''")
X'XBslashxFA' :: "Char" ("''\\xFA''")
X'XBslashxFB' :: "Char" ("''\\xFB''")
X'XBslashxFC' :: "Char" ("''\\xFC''")
X'XBslashxFD' :: "Char" ("''\\xFD''")
X'XBslashxFE' :: "Char" ("''\\xFE''")
X'XBslashxFF' :: "Char" ("''\\xFF''")
X'XCBr' :: "Char" ("''')''")
X'XCSqBr' :: "Char" ("'']''")
X'XCaret' :: "Char" ("''^''")
X'XCcedil' :: "Char" ("''Ç''")
X'XColon' :: "Char" ("'':''")
X'XComma' :: "Char" ("'',''")
X'XDivide' :: "Char" ("''÷''")
X'XDollar' :: "Char" ("''$''")
X'XETH' :: "Char" ("''Ð''")
X'XEacute' :: "Char" ("''É''")
X'XEcirc' :: "Char" ("''Ê''")
X'XEgrave' :: "Char" ("''È''")
X'XEq' :: "Char" ("''=''")
X'XEuml' :: "Char" ("''Ë''")
X'XExclam' :: "Char" ("''!''")
X'XGrave' :: "Char" ("''`''")
X'XGt' :: "Char" ("''>''")
X'XHash' :: "Char" ("''#''")
X'XIacute' :: "Char" ("''Í''")
X'XIcirc' :: "Char" ("''Î''")
X'XIgrave' :: "Char" ("''Ì''")
X'XIuml' :: "Char" ("''Ï''")
X'XLBrace' :: "Char" ("''{''")
X'XLt' :: "Char" ("''<''")
X'XMinus' :: "Char" ("''-''")
X'XNtilde' :: "Char" ("''Ñ''")
X'XOBr' :: "Char" ("'''(''")
X'XOSlash' :: "Char" ("''Ø''")
X'XOSqBr' :: "Char" ("''[''")
X'XOacute' :: "Char" ("''Ó''")
X'XOcirc' :: "Char" ("''Ô''")
X'XOgrave' :: "Char" ("''Ò''")
X'XOtilde' :: "Char" ("''Õ''")
X'XOuml' :: "Char" ("''Ö''")
X'XPercent' :: "Char" ("''%''")
X'XPeriod' :: "Char" ("''.''")
X'XPlus' :: "Char" ("''+''")
X'XQuest' :: "Char" ("''?''")
X'XRBrace' :: "Char" ("''}''")
X'XSemi' :: "Char" ("'';''")
X'XSlash' :: "Char" ("'''/''")
X'XSlash_32' :: "Char" ("'' ''")
X'XTHORN' :: "Char" ("''Þ''")
X'XTilde' :: "Char" ("''~''")
X'XTimes' :: "Char" ("''×''")
X'XUacute' :: "Char" ("''Ú''")
X'XUcirc' :: "Char" ("''Û''")
X'XUgrave' :: "Char" ("''Ù''")
X'XUuml' :: "Char" ("''Ü''")
X'XVBar' :: "Char" ("''|''")
X'XX' :: "Char" ("''X''")
X'XYacute' :: "Char" ("''Ý''")
X'Xaacute' :: "Char" ("''á''")
X'Xacirc' :: "Char" ("''â''")
X'Xacute' :: "Char" ("''´''")
X'Xaelig' :: "Char" ("''æ''")
X'Xagrave' :: "Char" ("''à''")
X'Xaring' :: "Char" ("''å''")
X'Xatilde' :: "Char" ("''ã''")
X'Xauml' :: "Char" ("''ä''")
X'Xbrvbar' :: "Char" ("''¦''")
X'Xccedil' :: "Char" ("''ç''")
X'Xcedil' :: "Char" ("''¸''")
X'Xcent' :: "Char" ("''¢''")
X'Xcopy' :: "Char" ("''©''")
X'Xcurren' :: "Char" ("''¤''")
X'Xdeg' :: "Char" ("''°''")
X'Xeacute' :: "Char" ("''é''")
X'Xecirc' :: "Char" ("''ê''")
X'Xegrave' :: "Char" ("''è''")
X'Xeth' :: "Char" ("''ð''")
X'Xeuml' :: "Char" ("''ë''")
X'Xfrac34' :: "Char" ("''¾''")
X'Xhalf' :: "Char" ("''½''")
X'Xiacute' :: "Char" ("''í''")
X'Xicirc' :: "Char" ("''î''")
X'Xiexcl' :: "Char" ("''¡''")
X'Xigrave' :: "Char" ("''ì''")
X'Xiquest' :: "Char" ("''¿''")
X'Xiuml' :: "Char" ("''ï''")
X'Xlaquo' :: "Char" ("''«''")
X'Xmacr' :: "Char" ("''¯''")
X'Xmicro' :: "Char" ("''µ''")
X'Xmiddot' :: "Char" ("''·''")
X'Xnbsp' :: "Char" ("'' ''")
X'Xnot' :: "Char" ("''¬''")
X'Xntilde' :: "Char" ("''ñ''")
X'Xoacute' :: "Char" ("''ó''")
X'Xocirc' :: "Char" ("''ô''")
X'Xograve' :: "Char" ("''ò''")
X'Xordf' :: "Char" ("''ª''")
X'Xordm' :: "Char" ("''º''")
X'Xoslash' :: "Char" ("''ø''")
X'Xotilde' :: "Char" ("''õ''")
X'Xouml' :: "Char" ("''ö''")
X'Xpara' :: "Char" ("''¶''")
X'Xplusmn' :: "Char" ("''±''")
X'Xpound' :: "Char" ("''£''")
X'Xquarter' :: "Char" ("''¼''")
X'Xraquo' :: "Char" ("''»''")
X'Xreg' :: "Char" ("''®''")
X'Xsect' :: "Char" ("''§''")
X'Xshy' :: "Char" ("''­''")
X'Xsup1' :: "Char" ("''¹''")
X'Xsup2' :: "Char" ("''²''")
X'Xsup3' :: "Char" ("''³''")
X'Xszlig' :: "Char" ("''ß''")
X'Xthorn' :: "Char" ("''þ''")
X'Xuacute' :: "Char" ("''ú''")
X'Xucirc' :: "Char" ("''û''")
X'Xugrave' :: "Char" ("''ù''")
X'Xuml' :: "Char" ("''¨''")
X'Xuuml' :: "Char" ("''ü''")
X'Xx' :: "Char" ("''*''")
X'Xyacute' :: "Char" ("''ý''")
X'Xyen' :: "Char" ("''¥''")
X'Xyuml' :: "Char" ("''ÿ''")
X'Y' :: "Char" ("''Y''")
X'Z' :: "Char" ("''Z''")
X'_' :: "Char" ("'''_''")
X'a' :: "Char" ("''a''")
X'b' :: "Char" ("''b''")
X'c' :: "Char" ("''c''")
X'd' :: "Char" ("''d''")
X'e' :: "Char" ("''e''")
X'f' :: "Char" ("''f''")
X'g' :: "Char" ("''g''")
X'h' :: "Char" ("''h''")
X'i' :: "Char" ("''i''")
X'j' :: "Char" ("''j''")
X'k' :: "Char" ("''k''")
X'l' :: "Char" ("''l''")
X'm' :: "Char" ("''m''")
X'n' :: "Char" ("''n''")
X'o' :: "Char" ("''o''")
X'p' :: "Char" ("''p''")
X'q' :: "Char" ("''q''")
X'r' :: "Char" ("''r''")
X's' :: "Char" ("''s''")
X't' :: "Char" ("''t''")
X'u' :: "Char" ("''u''")
X'v' :: "Char" ("''v''")
X'w' :: "Char" ("''w''")
X'x' :: "Char" ("''x''")
X'y' :: "Char" ("''y''")
X'z' :: "Char" ("''z''")
X0X1 :: "X_Int" ("0''")
X0X3 :: "Rat" ("0'_3")
X1X1 :: "X_Int" ("1''")
X1X2 :: "X_Nat" ("1''''")
X1X3 :: "Pos" ("1'_3")
X1X4 :: "Rat" ("1'_4")
X2X1 :: "X_Int" ("2''")
X2X2 :: "X_Nat" ("2''''")
X2X3 :: "Rat" ("2'_3")
X3X1 :: "X_Int" ("3''")
X3X2 :: "X_Nat" ("3''''")
X3X3 :: "Rat" ("3'_3")
X4X1 :: "X_Int" ("4''")
X4X2 :: "X_Nat" ("4''''")
X4X3 :: "Rat" ("4'_3")
X5X1 :: "X_Int" ("5''")
X5X2 :: "X_Nat" ("5''''")
X5X3 :: "Rat" ("5'_3")
X6X1 :: "X_Int" ("6''")
X6X2 :: "X_Nat" ("6''''")
X6X3 :: "Rat" ("6'_3")
X7X1 :: "X_Int" ("7''")
X7X2 :: "X_Nat" ("7''''")
X7X3 :: "Rat" ("7'_3")
X8X1 :: "X_Int" ("8''")
X8X2 :: "X_Nat" ("8''''")
X8X3 :: "Rat" ("8'_3")
X9X1 :: "X_Int" ("9''")
X9X2 :: "X_Nat" ("9''''")
X9X3 :: "Rat" ("9'_3")
XMinus__XX1 :: "X_Int => X_Int" ("(-''/ _)" [56] 56)
XMinus__XX2 :: "Rat => Rat" ("(-''''/ _)" [56] 56)
X_Cons :: "'a partial => 'a List partial => 'a List partial"
X_Nil :: "'a List" ("Nil''")
X__XAmpXAmp__X :: "bool => bool => bool" ("(_/ &&/ _)" [54,54] 52)
X__XAtXAt__X :: "X_Nat => X_Nat => X_Nat" ("(_/ @@/ _)" [54,54] 52)
X__XCaret__XX1 :: "X_Int => X_Nat => X_Int" ("(_/ ^''/ _)" [54,54] 52)
X__XCaret__XX2 :: "X_Nat => X_Nat => X_Nat" ("(_/ ^''''/ _)" [54,54] 52)
X__XCaret__XX3 :: "Rat => X_Int => Rat partial" ("(_/ ^'_3/ _)" [54,54] 52)
X__XEqXEq__X :: "'a partial => 'a partial => bool" ("(_/ ==''/ _)" [54,54] 52)
X__XExclam :: "X_Nat => X_Nat" ("(_/ !'')" [58] 58)
X__XGtXEq__XX1 :: "X_Int => X_Int => bool" ("(_/ >=''/ _)" [44,44] 42)
X__XGtXEq__XX2 :: "X_Nat => X_Nat => bool" ("(_/ >=''''/ _)" [44,44] 42)
X__XGtXEq__XX3 :: "Rat => Rat => bool" ("(_/ >='_3/ _)" [44,44] 42)
X__XGtXEq__XX4 :: "'a partial => 'a partial => bool" ("(_/ >='_4/ _)" [54,54] 52)
X__XGt__XX1 :: "X_Int => X_Int => bool" ("(_/ >''/ _)" [44,44] 42)
X__XGt__XX2 :: "X_Nat => X_Nat => bool" ("(_/ >''''/ _)" [44,44] 42)
X__XGt__XX3 :: "Rat => Rat => bool" ("(_/ >'_3/ _)" [44,44] 42)
X__XGt__XX4 :: "'a partial => 'a partial => bool" ("(_/ >'_4/ _)" [54,54] 52)
X__XLtXEq__XX1 :: "X_Int => X_Int => bool" ("(_/ <=''/ _)" [44,44] 42)
X__XLtXEq__XX2 :: "X_Nat => X_Nat => bool" ("(_/ <=''''/ _)" [44,44] 42)
X__XLtXEq__XX3 :: "Rat => Rat => bool" ("(_/ <='_3/ _)" [44,44] 42)
X__XLtXEq__XX4 :: "'a partial => 'a partial => bool" ("(_/ <='_4/ _)" [54,54] 52)
X__XLt__XX1 :: "X_Int => X_Int => bool" ("(_/ <''/ _)" [44,44] 42)
X__XLt__XX2 :: "X_Nat => X_Nat => bool" ("(_/ <''''/ _)" [44,44] 42)
X__XLt__XX3 :: "Rat => Rat => bool" ("(_/ <'_3/ _)" [44,44] 42)
X__XLt__XX4 :: "'a partial => 'a partial => bool" ("(_/ <'_4/ _)" [54,54] 52)
X__XMinusXExclam__X :: "X_Nat => X_Nat => X_Nat" ("(_/ -!/ _)" [54,54] 52)
X__XMinusXQuest__X :: "X_Nat => X_Nat => X_Nat partial" ("(_/ -?/ _)" [54,54] 52)
X__XMinus__XX1 :: "X_Int => X_Int => X_Int" ("(_/ -''/ _)" [54,54] 52)
X__XMinus__XX2 :: "X_Nat => X_Nat => X_Int" ("(_/ -''''/ _)" [54,54] 52)
X__XMinus__XX3 :: "Rat => Rat => Rat" ("(_/ -'_3/ _)" [54,54] 52)
X__XMinus__XX4 :: "'a partial => 'a partial => 'a partial" ("(_/ -'_4/ _)" [54,54] 52)
X__XPlusXPlus__X :: "'a List partial => 'a List partial => 'a List partial" ("(_/ ++''/ _)" [54,54] 52)
X__XPlus__XX1 :: "X_Int => X_Int => X_Int" ("(_/ +''/ _)" [54,54] 52)
X__XPlus__XX2 :: "X_Nat => X_Nat => X_Nat" ("(_/ +''''/ _)" [54,54] 52)
X__XPlus__XX3 :: "X_Nat => Pos => Pos" ("(_/ +'_3/ _)" [54,54] 52)
X__XPlus__XX4 :: "Pos => X_Nat => Pos" ("(_/ +'_4/ _)" [54,54] 52)
X__XPlus__XX5 :: "Rat => Rat => Rat" ("(_/ +'_5/ _)" [54,54] 52)
X__XPlus__XX6 :: "'a partial => 'a partial => 'a partial" ("(_/ +'_6/ _)" [54,54] 52)
X__XSlashXEq__X :: "'a partial => 'a partial => bool" ("(_/ '/=/ _)" [54,54] 52)
X__XSlashXQuest__XX1 :: "X_Int => X_Int => X_Int partial" ("(_/ '/?''/ _)" [54,54] 52)
X__XSlashXQuest__XX2 :: "X_Nat => X_Nat => X_Nat partial" ("(_/ '/?''''/ _)" [54,54] 52)
X__XSlash__XX1 :: "X_Int => Pos => Rat" ("(_/ '/''/ _)" [54,54] 52)
X__XSlash__XX2 :: "Rat => Rat => Rat partial" ("(_/ '/''''/ _)" [54,54] 52)
X__XSlash__XX3 :: "'a partial => 'a partial => 'a partial" ("(_/ '/'_3/ _)" [54,54] 52)
X__XVBarXVBar__X :: "bool => bool => bool" ("(_/ ||/ _)" [54,54] 52)
X__Xx__XX1 :: "X_Int => X_Int => X_Int" ("(_/ *''/ _)" [54,54] 52)
X__Xx__XX2 :: "X_Nat => X_Nat => X_Nat" ("(_/ *''''/ _)" [54,54] 52)
X__Xx__XX3 :: "Pos => Pos => Pos" ("(_/ *'_3/ _)" [54,54] 52)
X__Xx__XX4 :: "Rat => Rat => Rat" ("(_/ *'_4/ _)" [54,54] 52)
X__Xx__XX5 :: "'a partial => 'a partial => 'a partial" ("(_/ *'_5/ _)" [54,54] 52)
X__div__XX1 :: "X_Int => X_Int => X_Int partial" ("(_/ div''/ _)" [54,54] 52)
X__div__XX2 :: "X_Nat => X_Nat => X_Nat partial" ("(_/ div''''/ _)" [54,54] 52)
X__div__XX3 :: "'a partial => 'a partial => 'a partial" ("(_/ div'_3/ _)" [54,54] 52)
X__dvd__X :: "X_Nat => X_Nat => bool" ("(_/ dvd''/ _)" [44,44] 42)
X__mod__XX1 :: "X_Int => X_Int => X_Nat partial" ("(_/ mod''/ _)" [54,54] 52)
X__mod__XX2 :: "X_Nat => X_Nat => X_Nat partial" ("(_/ mod''''/ _)" [54,54] 52)
X__mod__XX3 :: "'a partial => 'a partial => 'a partial" ("(_/ mod'_3/ _)" [54,54] 52)
X__o__X :: "('b partial => 'c partial) * ('a partial => 'b partial) => 'a partial => 'c partial"
X__quot__XX1 :: "X_Int => X_Int => X_Int partial" ("(_/ quot''/ _)" [54,54] 52)
X__quot__XX2 :: "'a partial => 'a partial => 'a partial" ("(_/ quot''''/ _)" [54,54] 52)
X__rem__XX1 :: "X_Int => X_Int => X_Int partial" ("(_/ rem''/ _)" [54,54] 52)
X__rem__XX2 :: "'a partial => 'a partial => 'a partial" ("(_/ rem''''/ _)" [54,54] 52)
X_absX1 :: "X_Int => X_Nat" ("abs''/'(_')" [3] 999)
X_absX2 :: "Rat => Rat" ("abs''''/'(_')" [3] 999)
X_absX3 :: "'a partial => 'a partial" ("abs'_3/'(_')" [3] 999)
X_chr :: "X_Nat => Char partial" ("chr/'(_')" [3] 999)
X_concat :: "'a List List partial => 'a List partial" ("concat''/'(_')" [3] 999)
X_curry :: "('a partial * 'b partial => 'c partial) => 'a partial => 'b partial => 'c partial"
X_dropWhile :: "('a partial => bool) => 'a List partial => 'a List partial"
X_evenX1 :: "X_Int => bool" ("even''/'(_')" [3] 999)
X_evenX2 :: "X_Nat => bool" ("even''''/'(_')" [3] 999)
X_filter :: "('a partial => bool) => 'a List partial => 'a List partial"
X_flip :: "('a partial => 'b partial => 'c partial) => 'b partial => 'a partial => 'c partial"
X_foldl :: "('a partial => 'b partial => 'a partial) => 'a partial => 'b List partial => 'a partial"
X_foldr :: "('a partial => 'b partial => 'b partial) => 'b partial => 'a List partial => 'b partial"
X_fromInteger :: "X_Int => 'a partial" ("fromInteger/'(_')" [3] 999)
X_fst :: "'a partial => 'b partial => 'a partial" ("fst''/'(_,/ _')" [3,3] 999)
X_gn_inj :: "'a => 'b" ("gn'_inj/'(_')" [3] 999)
X_gn_proj :: "'a => 'b partial" ("gn'_proj/'(_')" [3] 999)
X_gn_subt :: "'a => 'b => bool" ("gn'_subt/'(_,/ _')" [3,3] 999)
X_head :: "'a List partial => 'a partial" ("head/'(_')" [3] 999)
X_id :: "'a partial => 'a partial" ("id''/'(_')" [3] 999)
X_init :: "'a List partial => 'a List partial" ("init/'(_')" [3] 999)
X_insert :: "'d partial => 'd List partial => 'd List partial"
X_isDigit :: "Char => bool" ("isDigit/'(_')" [3] 999)
X_isLetter :: "Char => bool" ("isLetter/'(_')" [3] 999)
X_isPrintable :: "Char => bool" ("isPrintable/'(_')" [3] 999)
X_last :: "'a List partial => 'a partial" ("last''/'(_')" [3] 999)
X_map :: "('a partial => 'b partial) => 'a List partial => 'b List partial"
X_maxX1 :: "X_Int => X_Int => X_Int" ("max''/'(_,/ _')" [3,3] 999)
X_maxX2 :: "X_Nat => X_Nat => X_Nat" ("max''''/'(_,/ _')" [3,3] 999)
X_maxX3 :: "Rat => Rat => Rat" ("max'_3/'(_,/ _')" [3,3] 999)
X_maxX4 :: "'a partial => 'a partial => 'a partial"
X_maximum :: "'d List partial => 'd partial" ("maximum/'(_')" [3] 999)
X_minX1 :: "X_Int => X_Int => X_Int" ("min''/'(_,/ _')" [3,3] 999)
X_minX2 :: "X_Nat => X_Nat => X_Nat" ("min''''/'(_,/ _')" [3,3] 999)
X_minX3 :: "Rat => Rat => Rat" ("min'_3/'(_,/ _')" [3,3] 999)
X_minX4 :: "'a partial => 'a partial => 'a partial"
X_minimum :: "'d List partial => 'd partial" ("minimum/'(_')" [3] 999)
X_negate :: "'a partial => 'a partial" ("negate/'(_')" [3] 999)
X_null :: "'a List partial => bool" ("null''/'(_')" [3] 999)
X_oddX1 :: "X_Int => bool" ("odd''/'(_')" [3] 999)
X_oddX2 :: "X_Nat => bool" ("odd''''/'(_')" [3] 999)
X_ord :: "Char => X_Nat" ("ord''/'(_')" [3] 999)
X_pre :: "X_Nat => X_Nat partial" ("pre/'(_')" [3] 999)
X_recip :: "'a partial => 'a partial" ("recip/'(_')" [3] 999)
X_reverse :: "'a List partial => 'a List partial" ("reverse/'(_')" [3] 999)
X_sign :: "X_Int => X_Int" ("sign/'(_')" [3] 999)
X_signum :: "'a partial => 'a partial" ("signum/'(_')" [3] 999)
X_snd :: "'a partial => 'b partial => 'b partial" ("snd''/'(_,/ _')" [3,3] 999)
X_tail :: "'a List partial => 'a List partial" ("tail/'(_')" [3] 999)
X_takeWhile :: "('a partial => bool) => 'a List partial => 'a List partial"
X_toInteger :: "'a partial => X_Int" ("toInteger/'(_')" [3] 999)
X_unzip :: "('a partial * 'b partial) List partial => ('a List partial * 'b List partial) partial" ("unzip/'(_')" [3] 999)
X_zip :: "'a List partial => 'b List partial => ('a partial * 'b partial) List partial"
break :: "('a partial => bool) => 'a List partial => 'a List partial * 'a List partial"
compare :: "'a partial => 'a partial => Ordering partial"
concatMap :: "('a partial => 'b List partial) => 'a List partial => 'b List partial"
delete :: "'e partial => 'e List partial => 'e List partial"
divMod :: "'a partial => 'a partial => 'a partial * 'a partial"
foldl1 :: "('a partial => 'a partial => 'a partial) => 'a List partial => 'a partial"
foldr1 :: "('a partial => 'a partial => 'a partial) => 'a List partial => 'a partial"
otherwiseH :: "bool"
partition :: "('a partial => bool) => 'a List partial => 'a List partial * 'a List partial"
quotRem :: "'a partial => 'a partial => 'a partial * 'a partial"
scanl :: "('a partial => 'b partial => 'a partial) => 'a partial => 'b List partial => 'a List partial"
scanl1 :: "('a partial => 'a partial => 'a partial) => 'a List partial => 'a List partial"
scanr :: "('a partial => 'b partial => 'b partial) => 'b partial => 'a List partial => 'b List partial"
scanr1 :: "('a partial => 'a partial => 'a partial) => 'a List partial => 'a List partial"
select :: "('a partial => bool) => 'a partial => 'a List partial * 'a List partial => 'a List partial * 'a List partial"
span :: "('a partial => bool) => 'a List partial => 'a List partial * 'a List partial"
sucX2 :: "X_Nat => Pos" ("suc''''/'(_')" [3] 999)
uncurry :: "('a partial => 'b partial => 'c partial) => 'a partial * 'b partial => 'c partial"

axioms
ga_subt_reflexive [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). gn_subt(x, y)"

ga_subt_transitive [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'b).
 ALL (z :: 'c). gn_subt(x, y) & gn_subt(y, z) --> gn_subt(x, z)"

ga_subt_inj_proj [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'b).
 gn_subt(x, y) -->
 y = (X_gn_inj :: 'a => 'b) x =
 (makePartial x = (X_gn_proj :: 'b => 'a partial) y)"

ga_inj_transitive [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'b).
 ALL (z :: 'c).
 gn_subt(x, y) & gn_subt(y, z) & y = (X_gn_inj :: 'a => 'b) x -->
 z = (X_gn_inj :: 'a => 'c) x = (z = (X_gn_inj :: 'b => 'c) y)"

ga_subt_Int_XLt_Rat [rule_format] :
"ALL (x :: X_Int). ALL (y :: Rat). gn_subt(x, y)"

ga_subt_Nat_XLt_Int [rule_format] :
"ALL (x :: X_Nat). ALL (y :: X_Int). gn_subt(x, y)"

ga_subt_Pos_XLt_Nat [rule_format] :
"ALL (x :: Pos). ALL (y :: X_Nat). gn_subt(x, y)"

Comp1 [rule_format] :
"ALL (f :: 'b partial => 'c partial).
 ALL (g :: 'a partial => 'b partial).
 ALL (y :: 'a partial). X__o__X (f, g) y = f (g y)"

IdDef [rule_format] : "ALL (x :: 'a partial). id'(x) = x"

FlipDef [rule_format] :
"ALL (f :: 'a partial => 'b partial => 'c partial).
 ALL (x :: 'a partial). ALL (y :: 'b partial). X_flip f y x = f x y"

FstDef [rule_format] :
"ALL (x :: 'a partial). ALL (y :: 'b partial). fst'(x, y) = x"

SndDef [rule_format] :
"ALL (x :: 'a partial). ALL (y :: 'b partial). snd'(x, y) = y"

CurryDef [rule_format] :
"ALL (g :: 'a partial * 'b partial => 'c partial).
 ALL (x :: 'a partial).
 ALL (y :: 'b partial). X_curry g x y = g (x, y)"

UncurryDef [rule_format] :
"ALL (f :: 'a partial => 'b partial => 'c partial).
 ALL (x :: 'a partial).
 ALL (y :: 'b partial). uncurry f (x, y) = f x y"

NotFalse [rule_format] : "Not' False"

NotTrue [rule_format] : "~ Not' True"

AndFalse [rule_format] : "ALL (x :: bool). ~ False && x"

AndTrue [rule_format] : "ALL (x :: bool). True && x = x"

AndSym [rule_format] :
"ALL (x :: bool). ALL (y :: bool). x && y = y && x"

OrDef [rule_format] :
"ALL (x :: bool).
 ALL (y :: bool). x || y = Not' (Not' x && Not' y)"

OtherwiseDef [rule_format] : "otherwiseH"

NotFalse1 [rule_format] : "ALL (x :: bool). Not' x = (~ x)"

NotTrue1 [rule_format] : "ALL (x :: bool). ~ Not' x = x"

notNot1 [rule_format] : "ALL (x :: bool). (~ x) = Not' x"

notNot2 [rule_format] : "ALL (x :: bool). (~ ~ x) = (~ Not' x)"

EqualTDef [rule_format] :
"ALL (x :: 'a partial). ALL (y :: 'a partial). x = y --> x ==' y"

EqualSymDef [rule_format] :
"ALL (x :: 'a partial). ALL (y :: 'a partial). x ==' y = y ==' x"

EqualReflex [rule_format] : "ALL (x :: 'a partial). x ==' x"

EqualTransT [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial).
 ALL (z :: 'a partial). x ==' y & y ==' z --> x ==' z"

DiffDef [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). x /= y = Not' (x ==' y)"

DiffSymDef [rule_format] :
"ALL (x :: 'a partial). ALL (y :: 'a partial). x /= y = y /= x"

DiffTDef [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). x /= y = Not' (x ==' y)"

DiffFDef [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). (~ x /= y) = x ==' y"

TE1 [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). ~ x ==' y --> ~ x = y"

TE2 [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). Not' (x ==' y) = (~ x ==' y)"

TE3 [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). (~ Not' (x ==' y)) = x ==' y"

TE4 [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). (~ x ==' y) = (~ x ==' y)"

IUE1 [rule_format] : "makePartial () ==' makePartial ()"

IUE2 [rule_format] : "~ makePartial () /= makePartial ()"

IBE1 [rule_format] : "makePartial () ==' makePartial ()"

IBE2 [rule_format] : "undefinedOp ==' undefinedOp"

IBE3 [rule_format] : "~ undefinedOp ==' makePartial ()"

IBE4 [rule_format] : "~ makePartial () ==' undefinedOp"

IBE5 [rule_format] : "makePartial () /= undefinedOp"

IBE6 [rule_format] : "undefinedOp /= makePartial ()"

IBE7 [rule_format] : "Not' (makePartial () ==' undefinedOp)"

IBE8 [rule_format] : "~ Not' Not' (makePartial () ==' undefinedOp)"

IOE01 [rule_format] : "makePartial LT ==' makePartial LT"

IOE02 [rule_format] : "makePartial EQ ==' makePartial EQ"

IOE03 [rule_format] : "makePartial GT ==' makePartial GT"

IOE04 [rule_format] : "~ makePartial LT ==' makePartial EQ"

IOE05 [rule_format] : "~ makePartial LT ==' makePartial GT"

IOE06 [rule_format] : "~ makePartial EQ ==' makePartial GT"

IOE07 [rule_format] : "makePartial LT /= makePartial EQ"

IOE08 [rule_format] : "makePartial LT /= makePartial GT"

IOE09 [rule_format] : "makePartial EQ /= makePartial GT"

LeIrreflexivity [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). x ==' y --> ~ x <_4 y"

LeTAsymmetry [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). x <_4 y --> ~ y <_4 x"

LeTTransitive [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial).
 ALL (z :: 'a partial). x <_4 y & y <_4 z --> x <_4 z"

LeTTotal [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). (x <_4 y | y <_4 x) | x ==' y"

GeDef [rule_format] :
"ALL (x :: 'a partial). ALL (y :: 'a partial). x >_4 y = y <_4 x"

GeIrreflexivity [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). x ==' y --> ~ x >_4 y"

GeTAsymmetry [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). x >_4 y --> ~ y >_4 x"

GeTTransitive [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial).
 ALL (z :: 'a partial). (x >_4 y) && (y >_4 z) --> x >_4 z"

GeTTotal [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). ((x >_4 y) || (y >_4 x)) || (x ==' y)"

LeqDef [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). x <=_4 y = (x <_4 y) || (x ==' y)"

LeqReflexivity [rule_format] : "ALL (x :: 'a partial). x <=_4 x"

LeqTTransitive [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial).
 ALL (z :: 'a partial). (x <=_4 y) && (y <=_4 z) --> x <=_4 z"

LeqTTotal [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). (x <=_4 y) && (y <=_4 x) = x ==' y"

GeqDef [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). x >=_4 y = (x >_4 y) || (x ==' y)"

GeqReflexivity [rule_format] : "ALL (x :: 'a partial). x >=_4 x"

GeqTTransitive [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial).
 ALL (z :: 'a partial). (x >=_4 y) && (y >=_4 z) --> x >=_4 z"

GeqTTotal [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). (x >=_4 y) && (y >=_4 x) = x ==' y"

EqTSOrdRel [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). x ==' y = (~ x <_4 y & ~ x >_4 y)"

EqFSOrdRel [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). (~ x ==' y) = (x <_4 y | x >_4 y)"

EqTOrdRel [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). x ==' y = (x <=_4 y & x >=_4 y)"

EqFOrdRel [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). (~ x ==' y) = (x <=_4 y | x >=_4 y)"

EqTOrdTSubstE [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial).
 ALL (z :: 'a partial). x ==' y & y <_4 z --> x <_4 z"

EqTOrdFSubstE [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial).
 ALL (z :: 'a partial). x ==' y & ~ y <_4 z --> ~ x <_4 z"

EqTOrdTSubstD [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial).
 ALL (z :: 'a partial). x ==' y & z <_4 y --> z <_4 x"

EqTOrdFSubstD [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial).
 ALL (z :: 'a partial). x ==' y & ~ z <_4 y --> ~ z <_4 x"

LeTGeFEqFRel [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). x <_4 y = (~ x >_4 y & ~ x ==' y)"

LeFGeTEqTRel [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). (~ x <_4 y) = (x >_4 y | x ==' y)"

LeTGeTRel [rule_format] :
"ALL (x :: 'a partial). ALL (y :: 'a partial). x <_4 y = y >_4 x"

LeFGeFRel [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). (~ x <_4 y) = (~ y >_4 x)"

LeqTGetTRel [rule_format] :
"ALL (x :: 'a partial). ALL (y :: 'a partial). x <=_4 y = y >=_4 x"

LeqFGetFRel [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). (~ x <=_4 y) = (~ y >=_4 x)"

GeTLeTRel [rule_format] :
"ALL (x :: 'a partial). ALL (y :: 'a partial). x >_4 y = y <_4 x"

GeFLeFRel [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). (~ x >_4 y) = (~ y <_4 x)"

GeqTLeqTRel [rule_format] :
"ALL (x :: 'a partial). ALL (y :: 'a partial). x >=_4 y = y <=_4 x"

GeqFLeqFRel [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). (~ x >=_4 y) = (~ y <=_4 x)"

LeqTGeFRel [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). x <=_4 y = (~ x >_4 y)"

LeqFGeTRel [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). (~ x <=_4 y) = x >_4 y"

GeTLeFEqFRel [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). x >_4 y = (~ x <_4 y & ~ x ==' y)"

GeFLeTEqTRel [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). (~ x >_4 y) = (x <_4 y | x ==' y)"

GeqTLeFRel [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). x >=_4 y = (~ x <_4 y)"

GeqFLeTRel [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). (~ x >=_4 y) = x <_4 y"

LeqTLeTEqTRel [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). x <=_4 y = (x <_4 y | x ==' y)"

LeqFLeFEqFRel [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). (~ x <=_4 y) = (~ x <_4 y & ~ x ==' y)"

GeqTGeTEqTRel [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). x >=_4 y = (x >_4 y | x ==' y)"

GeqFGeFEqFRel [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). (~ x >=_4 y) = (~ x >_4 y & ~ x ==' y)"

LeTGeqFRel [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). x <_4 y = (~ x >=_4 y)"

GeTLeqFRel [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). x >_4 y = (~ x <=_4 y)"

LeLeqDiff [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). x <_4 y = (x <=_4 y) && (x /= y)"

CmpLTDef [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). compare x y ==' makePartial LT = x <_4 y"

CmpEQDef [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). compare x y ==' makePartial EQ = x ==' y"

CmpGTDef [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). compare x y ==' makePartial GT = x >_4 y"

MaxYDef [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). X_maxX4 x y ==' y = x <=_4 y"

MaxXDef [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). X_maxX4 x y ==' x = y <=_4 x"

MinXDef [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). X_minX4 x y ==' x = x <=_4 y"

MinYDef [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). X_minX4 x y ==' y = y <=_4 x"

MaxSym [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). X_maxX4 x y ==' y = X_maxX4 y x ==' y"

MinSym [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). X_minX4 x y ==' y = X_minX4 y x ==' y"

TO1 [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). (x ==' y | x <_4 y) = x <=_4 y"

TO2 [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). x ==' y --> ~ x <_4 y"

TO3 [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). Not' Not' (x <_4 y) | Not' (x <_4 y)"

TO4 [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). x <_4 y --> Not' (x ==' y)"

TO5 [rule_format] :
"ALL (w :: 'a partial).
 ALL (x :: 'a partial).
 ALL (y :: 'a partial).
 ALL (z :: 'a partial). (x <_4 y & y <_4 z) & z <_4 w --> x <_4 w"

TO6 [rule_format] :
"ALL (x :: 'a partial).
 ALL (z :: 'a partial). z <_4 x --> Not' (x <_4 z)"

TO7 [rule_format] :
"ALL (x :: 'a partial). ALL (y :: 'a partial). x <_4 y = y >_4 x"

IUO01 [rule_format] : "makePartial () <=_4 makePartial ()"

IUO02 [rule_format] : "~ makePartial () <_4 makePartial ()"

IUO03 [rule_format] : "makePartial () >=_4 makePartial ()"

IUO04 [rule_format] : "~ makePartial () >_4 makePartial ()"

IUO05 [rule_format] :
"X_maxX4 (makePartial ()) (makePartial ()) ==' makePartial ()"

IUO06 [rule_format] :
"X_minX4 (makePartial ()) (makePartial ()) ==' makePartial ()"

IUO07 [rule_format] :
"compare (makePartial ()) (makePartial ()) ==' makePartial EQ"

IOO13 [rule_format] : "makePartial LT <_4 makePartial EQ"

IOO14 [rule_format] : "makePartial EQ <_4 makePartial GT"

IOO15 [rule_format] : "makePartial LT <_4 makePartial GT"

IOO16 [rule_format] : "makePartial LT <=_4 makePartial EQ"

IOO17 [rule_format] : "makePartial EQ <=_4 makePartial GT"

IOO18 [rule_format] : "makePartial LT <=_4 makePartial GT"

IOO19 [rule_format] : "makePartial EQ >=_4 makePartial LT"

IOO20 [rule_format] : "makePartial GT >=_4 makePartial EQ"

IOO21 [rule_format] : "makePartial GT >=_4 makePartial LT"

IOO22 [rule_format] : "makePartial EQ >_4 makePartial LT"

IOO23 [rule_format] : "makePartial GT >_4 makePartial EQ"

IOO24 [rule_format] : "makePartial GT >_4 makePartial LT"

IOO25 [rule_format] :
"X_maxX4 (makePartial LT) (makePartial EQ) ==' makePartial EQ"

IOO26 [rule_format] :
"X_maxX4 (makePartial EQ) (makePartial GT) ==' makePartial GT"

IOO27 [rule_format] :
"X_maxX4 (makePartial LT) (makePartial GT) ==' makePartial GT"

IOO28 [rule_format] :
"X_minX4 (makePartial LT) (makePartial EQ) ==' makePartial LT"

IOO29 [rule_format] :
"X_minX4 (makePartial EQ) (makePartial GT) ==' makePartial EQ"

IOO30 [rule_format] :
"X_minX4 (makePartial LT) (makePartial GT) ==' makePartial LT"

IOO31 [rule_format] :
"compare (makePartial LT) (makePartial LT) ==' makePartial EQ"

IOO32 [rule_format] :
"compare (makePartial EQ) (makePartial EQ) ==' makePartial EQ"

IOO33 [rule_format] :
"compare (makePartial GT) (makePartial GT) ==' makePartial EQ"

IBO5 [rule_format] : "undefinedOp <_4 makePartial ()"

IBO6 [rule_format] : "~ undefinedOp >=_4 makePartial ()"

IBO7 [rule_format] : "makePartial () >=_4 undefinedOp"

IBO8 [rule_format] : "~ makePartial () <_4 undefinedOp"

IBO9 [rule_format] :
"X_maxX4 undefinedOp (makePartial ()) ==' makePartial ()"

IBO10 [rule_format] :
"X_minX4 undefinedOp (makePartial ()) ==' undefinedOp"

IBO11 [rule_format] :
"compare (makePartial ()) (makePartial ()) ==' makePartial EQ"

IBO12 [rule_format] :
"compare undefinedOp undefinedOp ==' makePartial EQ"

NotDefHead [rule_format] : "~ defOp (head(makePartial Nil'))"

HeadDef [rule_format] :
"ALL (x :: 'a partial).
 ALL (xs :: 'a List partial). head(X_Cons x xs) = x"

NotDefTail [rule_format] : "~ defOp (tail(makePartial Nil'))"

TailDef [rule_format] :
"ALL (x :: 'a partial).
 ALL (xs :: 'a List partial). tail(X_Cons x xs) = xs"

FoldrNil [rule_format] :
"ALL (f :: 'a partial => 'b partial => 'b partial).
 ALL (s :: 'b partial). X_foldr f s (makePartial Nil') = s"

FoldrCons [rule_format] :
"ALL (f :: 'a partial => 'b partial => 'b partial).
 ALL (s :: 'b partial).
 ALL (x :: 'a partial).
 ALL (xs :: 'a List partial).
 X_foldr f s (X_Cons x xs) = f x (X_foldr f s xs)"

FoldlNil [rule_format] :
"ALL (g :: 'a partial => 'b partial => 'a partial).
 ALL (t :: 'a partial). X_foldl g t (makePartial Nil') = t"

FoldlCons [rule_format] :
"ALL (g :: 'a partial => 'b partial => 'a partial).
 ALL (t :: 'a partial).
 ALL (z :: 'b partial).
 ALL (zs :: 'b List partial).
 X_foldl g t (X_Cons z zs) = X_foldl g (g t z) zs"

MapNil [rule_format] :
"ALL (h :: 'a partial => 'b partial).
 X_map h (makePartial Nil') = makePartial Nil'"

MapCons [rule_format] :
"ALL (h :: 'a partial => 'b partial).
 ALL (x :: 'a partial).
 ALL (xs :: 'a List partial).
 X_map h (X_Cons x xs) = X_Cons (h x) (X_map h xs)"

XPlusXPlusNil [rule_format] :
"ALL (l :: 'a List partial). makePartial Nil' ++' l = l"

XPlusXPlusCons [rule_format] :
"ALL (l :: 'a List partial).
 ALL (x :: 'a partial).
 ALL (xs :: 'a List partial).
 X_Cons x xs ++' l = X_Cons x (xs ++' l)"

FilterNil [rule_format] :
"ALL (p :: 'a partial => bool).
 X_filter p (makePartial Nil') = makePartial Nil'"

FilterConsT [rule_format] :
"ALL (p :: 'a partial => bool).
 ALL (x :: 'a partial).
 ALL (xs :: 'a List partial).
 p x --> X_filter p (X_Cons x xs) = X_Cons x (X_filter p xs)"

FilterConsF [rule_format] :
"ALL (p :: 'a partial => bool).
 ALL (x :: 'a partial).
 ALL (xs :: 'a List partial).
 ~ p x --> X_filter p (X_Cons x xs) = X_filter p xs"

ZipNil [rule_format] :
"ALL (l :: 'a List partial).
 X_zip (makePartial Nil') l = makePartial Nil'"

ZipConsNil [rule_format] :
"ALL (l :: 'a List partial).
 ALL (x :: 'a partial).
 ALL (xs :: 'a List partial).
 l = makePartial Nil' --> X_zip (X_Cons x xs) l = makePartial Nil'"

ZipConsCons [rule_format] :
"ALL (l :: 'a List partial).
 ALL (x :: 'a partial).
 ALL (xs :: 'a List partial).
 ALL (y :: 'a partial).
 ALL (ys :: 'a List partial).
 l = X_Cons y ys -->
 X_zip (X_Cons x xs) l = X_Cons (makePartial (x, y)) (X_zip xs ys)"

UnzipNil [rule_format] :
"mapSnd id (mapFst id (unzip(makePartial Nil'))) =
 makePartial (makePartial Nil', makePartial Nil')"

UnzipCons [rule_format] :
"ALL (ps :: ('a partial * 'b partial) List partial).
 ALL (x :: 'a partial).
 ALL (ys :: 'a List partial).
 ALL (z :: 'b partial).
 ALL (zs :: 'b List partial).
 makePartial (ys, zs) = mapSnd id (mapFst id (unzip(ps))) -->
 mapSnd id (mapFst id (unzip(X_Cons (makePartial (x, z)) ps))) =
 makePartial (X_Cons x ys, X_Cons z zs)"

ILE01 [rule_format] : "makePartial Nil' ==' makePartial Nil'"

ILE02 [rule_format] :
"ALL (x :: 'a partial).
 ALL (xs :: 'a List partial).
 ALL (y :: 'a partial).
 ALL (ys :: 'a List partial).
 X_Cons x xs ==' X_Cons y ys = (x ==' y) && (xs ==' ys)"

ILO01 [rule_format] : "~ makePartial Nil' <_4 makePartial Nil'"

ILO02 [rule_format] : "makePartial Nil' <=_4 makePartial Nil'"

ILO03 [rule_format] : "~ makePartial Nil' >_4 makePartial Nil'"

ILO04 [rule_format] : "makePartial Nil' >=_4 makePartial Nil'"

ILO05 [rule_format] :
"ALL (w :: 'b partial).
 ALL (ws :: 'b List partial).
 ALL (z :: 'b partial).
 ALL (zs :: 'b List partial).
 z <_4 w --> X_Cons z zs <_4 X_Cons w ws"

ILO06 [rule_format] :
"ALL (w :: 'b partial).
 ALL (ws :: 'b List partial).
 ALL (z :: 'b partial).
 ALL (zs :: 'b List partial).
 z ==' w --> X_Cons z zs <_4 X_Cons w ws = zs <_4 ws"

ILO07 [rule_format] :
"ALL (w :: 'b partial).
 ALL (ws :: 'b List partial).
 ALL (z :: 'b partial).
 ALL (zs :: 'b List partial).
 ~ z <_4 w & ~ z ==' w --> ~ X_Cons z zs <_4 X_Cons w ws"

ILO08 [rule_format] :
"ALL (w :: 'b partial).
 ALL (ws :: 'b List partial).
 ALL (z :: 'b partial).
 ALL (zs :: 'b List partial).
 X_Cons z zs <=_4 X_Cons w ws =
 (X_Cons z zs <_4 X_Cons w ws) || (X_Cons z zs ==' X_Cons w ws)"

ILO09 [rule_format] :
"ALL (w :: 'b partial).
 ALL (ws :: 'b List partial).
 ALL (z :: 'b partial).
 ALL (zs :: 'b List partial).
 X_Cons z zs >_4 X_Cons w ws = X_Cons w ws <_4 X_Cons z zs"

ILO10 [rule_format] :
"ALL (w :: 'b partial).
 ALL (ws :: 'b List partial).
 ALL (z :: 'b partial).
 ALL (zs :: 'b List partial).
 X_Cons z zs >=_4 X_Cons w ws =
 (X_Cons z zs >_4 X_Cons w ws) || (X_Cons z zs ==' X_Cons w ws)"

ILO11 [rule_format] :
"compare (makePartial Nil') (makePartial Nil') ==' makePartial EQ =
 makePartial Nil' ==' makePartial Nil'"

ILO12 [rule_format] :
"compare (makePartial Nil') (makePartial Nil') ==' makePartial LT =
 makePartial Nil' <_4 makePartial Nil'"

ILO13 [rule_format] :
"compare (makePartial Nil') (makePartial Nil') ==' makePartial GT =
 makePartial Nil' >_4 makePartial Nil'"

ILO14 [rule_format] :
"ALL (w :: 'b partial).
 ALL (ws :: 'b List partial).
 ALL (z :: 'b partial).
 ALL (zs :: 'b List partial).
 compare (X_Cons z zs) (X_Cons w ws) ==' makePartial EQ =
 X_Cons z zs ==' X_Cons w ws"

ILO15 [rule_format] :
"ALL (w :: 'b partial).
 ALL (ws :: 'b List partial).
 ALL (z :: 'b partial).
 ALL (zs :: 'b List partial).
 compare (X_Cons z zs) (X_Cons w ws) ==' makePartial LT =
 X_Cons z zs <_4 X_Cons w ws"

ILO16 [rule_format] :
"ALL (w :: 'b partial).
 ALL (ws :: 'b List partial).
 ALL (z :: 'b partial).
 ALL (zs :: 'b List partial).
 compare (X_Cons z zs) (X_Cons w ws) ==' makePartial GT =
 X_Cons z zs >_4 X_Cons w ws"

ILO17 [rule_format] :
"X_maxX4 (makePartial Nil') (makePartial Nil') =='
 makePartial Nil' =
 makePartial Nil' <=_4 makePartial Nil'"

ILO18 [rule_format] :
"X_minX4 (makePartial Nil') (makePartial Nil') =='
 makePartial Nil' =
 makePartial Nil' <=_4 makePartial Nil'"

ILO19 [rule_format] :
"ALL (w :: 'b partial).
 ALL (ws :: 'b List partial).
 ALL (z :: 'b partial).
 ALL (zs :: 'b List partial).
 X_Cons z zs <=_4 X_Cons w ws =
 X_maxX4 (X_Cons z zs) (X_Cons w ws) ==' X_Cons w ws"

ILO20 [rule_format] :
"ALL (w :: 'b partial).
 ALL (ws :: 'b List partial).
 ALL (z :: 'b partial).
 ALL (zs :: 'b List partial).
 X_Cons w ws <=_4 X_Cons z zs =
 X_maxX4 (X_Cons z zs) (X_Cons w ws) ==' X_Cons z zs"

ILO21 [rule_format] :
"ALL (w :: 'b partial).
 ALL (ws :: 'b List partial).
 ALL (z :: 'b partial).
 ALL (zs :: 'b List partial).
 X_Cons z zs <=_4 X_Cons w ws =
 X_minX4 (X_Cons z zs) (X_Cons w ws) ==' X_Cons z zs"

ILO22 [rule_format] :
"ALL (w :: 'b partial).
 ALL (ws :: 'b List partial).
 ALL (z :: 'b partial).
 ALL (zs :: 'b List partial).
 X_Cons w ws <=_4 X_Cons z zs =
 X_minX4 (X_Cons z zs) (X_Cons w ws) ==' X_Cons w ws"

FoldlDecomp [rule_format] :
"ALL (e :: 'a partial).
 ALL (i :: 'a partial => 'b partial => 'a partial).
 ALL (ts :: 'b List partial).
 ALL (ys :: 'b List partial).
 X_foldl i e (ys ++' ts) = X_foldl i (X_foldl i e ys) ts"

MapDecomp [rule_format] :
"ALL (f :: 'a partial => 'b partial).
 ALL (xs :: 'a List partial).
 ALL (zs :: 'a List partial).
 X_map f (xs ++' zs) = X_map f xs ++' X_map f zs"

MapFunctor [rule_format] :
"ALL (f :: 'a partial => 'b partial).
 ALL (g :: 'b partial => 'c partial).
 ALL (xs :: 'a List partial).
 X_map (X__o__X (g, f)) xs = X_map g (X_map f xs)"

FilterProm [rule_format] :
"ALL (f :: 'a partial => 'b partial).
 ALL (p :: 'b partial => bool).
 ALL (xs :: 'a List partial).
 X_filter p (X_map f xs) =
 X_map f (X_filter (id o defOp o X__o__X (bool2partial o p, f)) xs)"

InitNil [rule_format] : "~ defOp (init(makePartial Nil'))"

InitConsNil [rule_format] :
"ALL (x :: 'a partial).
 init(X_Cons x (makePartial Nil')) = makePartial Nil'"

InitConsCons [rule_format] :
"ALL (x :: 'a partial).
 ALL (xs :: 'a List partial).
 init(X_Cons x xs) = X_Cons x (init(xs))"

LastNil [rule_format] : "~ defOp (last'(makePartial Nil'))"

LastConsNil [rule_format] :
"ALL (x :: 'a partial). last'(X_Cons x (makePartial Nil')) = x"

LastConsCons [rule_format] :
"ALL (x :: 'a partial).
 ALL (xs :: 'a List partial). last'(X_Cons x xs) = last'(xs)"

NullNil [rule_format] : "null'(makePartial Nil')"

NullCons [rule_format] :
"ALL (x :: 'a partial).
 ALL (xs :: 'a List partial). ~ null'(X_Cons x xs)"

ReverseNil [rule_format] :
"reverse(makePartial Nil') = makePartial Nil'"

ReverseCons [rule_format] :
"ALL (x :: 'a partial).
 ALL (xs :: 'a List partial).
 reverse(X_Cons x xs) = reverse(xs) ++' X_Cons x (makePartial Nil')"

Foldr1Nil [rule_format] :
"ALL (f :: 'a partial => 'a partial => 'a partial).
 ~ defOp (foldr1 f (makePartial Nil'))"

Foldr1ConsNil [rule_format] :
"ALL (f :: 'a partial => 'a partial => 'a partial).
 ALL (x :: 'a partial). foldr1 f (X_Cons x (makePartial Nil')) = x"

Foldr1ConsCons [rule_format] :
"ALL (f :: 'a partial => 'a partial => 'a partial).
 ALL (x :: 'a partial).
 ALL (xs :: 'a List partial).
 foldr1 f (X_Cons x xs) = f x (foldr1 f xs)"

Foldl1Nil [rule_format] :
"ALL (f :: 'a partial => 'a partial => 'a partial).
 ~ defOp (foldl1 f (makePartial Nil'))"

Foldl1ConsNil [rule_format] :
"ALL (f :: 'a partial => 'a partial => 'a partial).
 ALL (x :: 'a partial). foldl1 f (X_Cons x (makePartial Nil')) = x"

Foldl1ConsCons [rule_format] :
"ALL (f :: 'a partial => 'a partial => 'a partial).
 ALL (x :: 'a partial).
 ALL (xs :: 'a List partial).
 foldl1 f (X_Cons x xs) = f x (foldr1 f xs)"

ScanlNil [rule_format] :
"ALL (g :: 'a partial => 'a partial => 'a partial).
 ALL (q :: 'a partial).
 ALL (xs :: 'a List partial).
 xs = makePartial Nil' -->
 scanl g q xs = X_Cons q (makePartial Nil')"

ScanlCons [rule_format] :
"ALL (g :: 'a partial => 'a partial => 'a partial).
 ALL (q :: 'a partial).
 ALL (r :: 'a partial).
 ALL (rs :: 'a List partial).
 ALL (xs :: 'a List partial).
 xs = X_Cons r rs --> scanl g q xs = X_Cons q (scanl g (g q r) rs)"

Scanl1Nil [rule_format] :
"ALL (f :: 'a partial => 'a partial => 'a partial).
 scanl1 f (makePartial Nil') = makePartial Nil'"

Scanl1Cons [rule_format] :
"ALL (f :: 'a partial => 'a partial => 'a partial).
 ALL (x :: 'a partial).
 ALL (xs :: 'a List partial). scanl1 f (X_Cons x xs) = scanl f x xs"

ScanrNil [rule_format] :
"ALL (h :: 'a partial => 'a partial => 'a partial).
 ALL (q :: 'a partial).
 scanr h q (makePartial Nil') = X_Cons q (makePartial Nil')"

ScanrCons [rule_format] :
"ALL (h :: 'a partial => 'a partial => 'a partial).
 ALL (q :: 'a partial).
 ALL (r :: 'a partial).
 ALL (rs :: 'a List partial).
 ALL (x :: 'a partial).
 ALL (xs :: 'a List partial).
 X_Cons r rs = scanr h q xs -->
 scanr h q (X_Cons x xs) = X_Cons (h x r) (X_Cons r rs)"

Scanr1Nil [rule_format] :
"ALL (f :: 'a partial => 'a partial => 'a partial).
 scanr1 f (makePartial Nil') = makePartial Nil'"

Scanr1ConsNil [rule_format] :
"ALL (f :: 'a partial => 'a partial => 'a partial).
 ALL (x :: 'a partial).
 scanr1 f (X_Cons x (makePartial Nil')) =
 X_Cons x (makePartial Nil')"

Scanr1ConsCons [rule_format] :
"ALL (f :: 'a partial => 'a partial => 'a partial).
 ALL (q :: 'a partial).
 ALL (qs :: 'a List partial).
 ALL (x :: 'a partial).
 ALL (xs :: 'a List partial).
 X_Cons q qs = scanr1 f xs -->
 scanr1 f (X_Cons x xs) = X_Cons (f x q) (X_Cons q qs)"

ScanlProperty [rule_format] :
"ALL (g :: 'a partial => 'a partial => 'a partial).
 ALL (x :: 'a partial).
 ALL (xs :: 'a List partial). last'(scanl g x xs) = X_foldl g x xs"

ScanrProperty [rule_format] :
"ALL (h :: 'a partial => 'a partial => 'a partial).
 ALL (x :: 'a partial).
 ALL (xs :: 'a List partial). head(scanr h x xs) = X_foldr h x xs"

ConcatDef [rule_format] :
"ALL (xxs :: 'a List List partial).
 concat'(xxs) =
 X_foldr (X_curry (uncurryOp X__XPlusXPlus__X)) (makePartial Nil')
 xxs"

ConcatMapDef [rule_format] :
"ALL (g :: 'a partial => 'b List partial).
 ALL (xs :: 'a List partial). concatMap g xs = concat'(X_map g xs)"

MaximunNil [rule_format] : "~ defOp (maximum(makePartial Nil'))"

MaximumDef [rule_format] :
"ALL (ds :: 'd List partial). maximum(ds) = foldl1 X_maxX4 ds"

MinimunNil [rule_format] : "~ defOp (minimum(makePartial Nil'))"

MinimumDef [rule_format] :
"ALL (ds :: 'd List partial). minimum(ds) = foldl1 X_minX4 ds"

TakeWhileNil [rule_format] :
"ALL (p :: 'a partial => bool).
 X_takeWhile p (makePartial Nil') = makePartial Nil'"

TakeWhileConsT [rule_format] :
"ALL (p :: 'a partial => bool).
 ALL (x :: 'a partial).
 ALL (xs :: 'a List partial).
 p x --> X_takeWhile p (X_Cons x xs) = X_Cons x (X_takeWhile p xs)"

TakeWhileConsF [rule_format] :
"ALL (p :: 'a partial => bool).
 ALL (x :: 'a partial).
 ALL (xs :: 'a List partial).
 ~ p x --> X_takeWhile p (X_Cons x xs) = makePartial Nil'"

DropWhileNil [rule_format] :
"ALL (p :: 'a partial => bool).
 X_dropWhile p (makePartial Nil') = makePartial Nil'"

DropWhileConsT [rule_format] :
"ALL (p :: 'a partial => bool).
 ALL (x :: 'a partial).
 ALL (xs :: 'a List partial).
 p x --> X_dropWhile p (X_Cons x xs) = X_dropWhile p xs"

DropWhileConsF [rule_format] :
"ALL (p :: 'a partial => bool).
 ALL (x :: 'a partial).
 ALL (xs :: 'a List partial).
 ~ p x --> X_dropWhile p (X_Cons x xs) = X_Cons x xs"

SpanNil [rule_format] :
"ALL (p :: 'a partial => bool).
 mapSnd id (mapFst id (span p (makePartial Nil'))) =
 (makePartial Nil', makePartial Nil')"

SpanConsT [rule_format] :
"ALL (p :: 'a partial => bool).
 ALL (x :: 'a partial).
 ALL (xs :: 'a List partial).
 p x -->
 mapSnd id (mapFst id (span p (X_Cons x xs))) =
 mapSnd id
 (mapFst id (let (ys, zs) = span p xs in (X_Cons x ys, zs)))"

SpanConsF [rule_format] :
"ALL (p :: 'a partial => bool).
 ALL (x :: 'a partial).
 ALL (xs :: 'a List partial).
 ~ p x -->
 mapSnd id (mapFst id (span p (X_Cons x xs))) =
 mapSnd id
 (mapFst (id o makePartial)
  (let (ys, zs) = span p xs in (Nil', X_Cons x xs)))"

SpanThm [rule_format] :
"ALL (p :: 'a partial => bool).
 ALL (xs :: 'a List partial).
 mapSnd id (mapFst id (span p xs)) =
 (X_takeWhile p xs, X_dropWhile p xs)"

BreakDef [rule_format] :
"ALL (p :: 'a partial => bool).
 ALL (xs :: 'a List partial).
 mapSnd id (mapFst id (break p xs)) =
 mapSnd id
 (mapFst id
  (let q =
       id o defOp o
       X__o__X (bool2partial o notH__X o defOp, bool2partial o p)
   in span q xs))"

BreakThm [rule_format] :
"ALL (p :: 'a partial => bool).
 ALL (xs :: 'a List partial).
 mapSnd id (mapFst id (break p xs)) =
 mapSnd id
 (mapFst id
  (span
   (id o defOp o
    X__o__X (bool2partial o notH__X o defOp, bool2partial o p))
   xs))"

InsertNil [rule_format] :
"ALL (q :: 'd partial).
 X_insert q (makePartial Nil') = X_Cons q (makePartial Nil')"

InsertCons1 [rule_format] :
"ALL (q :: 'd partial).
 ALL (r :: 'd partial).
 ALL (rs :: 'd List partial).
 q <=_4 r --> X_insert q (X_Cons r rs) = X_Cons q (X_Cons r rs)"

InsertCons2 [rule_format] :
"ALL (q :: 'd partial).
 ALL (r :: 'd partial).
 ALL (rs :: 'd List partial).
 q >_4 r --> X_insert q (X_Cons r rs) = X_Cons r (X_insert q rs)"

DeleteNil [rule_format] :
"ALL (s :: 'e partial).
 delete s (makePartial Nil') = makePartial Nil'"

DeleteConsT [rule_format] :
"ALL (s :: 'e partial).
 ALL (t :: 'e partial).
 ALL (ts :: 'e List partial).
 s ==' t --> delete s (X_Cons t ts) = ts"

DeleteConsF [rule_format] :
"ALL (s :: 'e partial).
 ALL (t :: 'e partial).
 ALL (ts :: 'e List partial).
 ~ s ==' t --> delete s (X_Cons t ts) = X_Cons t (delete s ts)"

SelectT [rule_format] :
"ALL (p :: 'a partial => bool).
 ALL (x :: 'a partial).
 ALL (xs :: 'a List partial).
 ALL (ys :: 'a List partial).
 p x -->
 mapSnd id (mapFst id (select p x (xs, ys))) = (X_Cons x xs, ys)"

SelectF [rule_format] :
"ALL (p :: 'a partial => bool).
 ALL (x :: 'a partial).
 ALL (xs :: 'a List partial).
 ALL (ys :: 'a List partial).
 ~ p x -->
 mapSnd id (mapFst id (select p x (xs, ys))) = (xs, X_Cons x ys)"

Partition [rule_format] :
"ALL (p :: 'a partial => bool).
 ALL (xs :: 'a List partial).
 makePartial (mapSnd id (mapFst id (partition p xs))) =
 mapSnd id
 (mapFst id
  (X_foldr (comp makePartial o flip comp makeTotal o select p)
   (makePartial (makePartial Nil', makePartial Nil')) xs))"

PartitionProp [rule_format] :
"ALL (p :: 'a partial => bool).
 ALL (xs :: 'a List partial).
 mapSnd id (mapFst id (partition p xs)) =
 (X_filter p xs,
  X_filter
  (id o defOp o
   X__o__X (bool2partial o notH__X o defOp, bool2partial o p))
  xs)"

ga_selector_pre [rule_format] :
"ALL (XX1 :: X_Nat). pre(suc'(XX1)) = makePartial XX1"

ga_injective_suc [rule_format] :
"ALL (XX1 :: X_Nat).
 ALL (Y1 :: X_Nat). suc'(XX1) = suc'(Y1) = (XX1 = Y1)"

ga_disjoint_0_suc [rule_format] :
"ALL (Y1 :: X_Nat). ~ 0'' = suc'(Y1)"

ga_selector_undef_pre_0 [rule_format] : "~ defOp (pre(0''))"

X1_def_Nat [rule_format] : "1'' = suc'(0'')"

X2_def_Nat [rule_format] : "2'' = suc'(1'')"

X3_def_Nat [rule_format] : "3'' = suc'(2'')"

X4_def_Nat [rule_format] : "4'' = suc'(3'')"

X5_def_Nat [rule_format] : "5'' = suc'(4'')"

X6_def_Nat [rule_format] : "6'' = suc'(5'')"

X7_def_Nat [rule_format] : "7'' = suc'(6'')"

X8_def_Nat [rule_format] : "8'' = suc'(7'')"

X9_def_Nat [rule_format] : "9'' = suc'(8'')"

decimal_def [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat). m @@ X_n = (m *'' suc'(9'')) +'' X_n"

ga_comm___XPlus__ [rule_format] :
"ALL (x :: X_Nat). ALL (y :: X_Nat). x +'' y = y +'' x"

ga_assoc___XPlus__ [rule_format] :
"ALL (x :: X_Nat).
 ALL (y :: X_Nat).
 ALL (z :: X_Nat). (x +'' y) +'' z = x +'' (y +'' z)"

ga_right_unit___XPlus__ [rule_format] :
"ALL (x :: X_Nat). x +'' 0'' = x"

ga_left_unit___XPlus__ [rule_format] :
"ALL (x :: X_Nat). 0'' +'' x = x"

ga_left_comm___XPlus__ [rule_format] :
"ALL (x :: X_Nat).
 ALL (y :: X_Nat).
 ALL (z :: X_Nat). x +'' (y +'' z) = y +'' (x +'' z)"

ga_comm___Xx__ [rule_format] :
"ALL (x :: X_Nat). ALL (y :: X_Nat). x *'' y = y *'' x"

ga_assoc___Xx__ [rule_format] :
"ALL (x :: X_Nat).
 ALL (y :: X_Nat).
 ALL (z :: X_Nat). (x *'' y) *'' z = x *'' (y *'' z)"

ga_right_unit___Xx__ [rule_format] :
"ALL (x :: X_Nat). x *'' 1'' = x"

ga_left_unit___Xx__ [rule_format] :
"ALL (x :: X_Nat). 1'' *'' x = x"

ga_left_comm___Xx__ [rule_format] :
"ALL (x :: X_Nat).
 ALL (y :: X_Nat).
 ALL (z :: X_Nat). x *'' (y *'' z) = y *'' (x *'' z)"

ga_comm_min [rule_format] :
"ALL (x :: X_Nat). ALL (y :: X_Nat). min''(x, y) = min''(y, x)"

ga_assoc_min [rule_format] :
"ALL (x :: X_Nat).
 ALL (y :: X_Nat).
 ALL (z :: X_Nat). min''(min''(x, y), z) = min''(x, min''(y, z))"

ga_left_comm_min [rule_format] :
"ALL (x :: X_Nat).
 ALL (y :: X_Nat).
 ALL (z :: X_Nat). min''(x, min''(y, z)) = min''(y, min''(x, z))"

ga_comm_max [rule_format] :
"ALL (x :: X_Nat). ALL (y :: X_Nat). max''(x, y) = max''(y, x)"

ga_assoc_max [rule_format] :
"ALL (x :: X_Nat).
 ALL (y :: X_Nat).
 ALL (z :: X_Nat). max''(max''(x, y), z) = max''(x, max''(y, z))"

ga_right_unit_max [rule_format] :
"ALL (x :: X_Nat). max''(x, 0'') = x"

ga_left_unit_max [rule_format] :
"ALL (x :: X_Nat). max''(0'', x) = x"

ga_left_comm_max [rule_format] :
"ALL (x :: X_Nat).
 ALL (y :: X_Nat).
 ALL (z :: X_Nat). max''(x, max''(y, z)) = max''(y, max''(x, z))"

leq_def1_Nat [rule_format] : "ALL (X_n :: X_Nat). 0'' <='' X_n"

dvd_def_Nat [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat).
 (m dvd' X_n) = (EX (k :: X_Nat). X_n = m *'' k)"

leq_def2_Nat [rule_format] :
"ALL (X_n :: X_Nat). ~ suc'(X_n) <='' 0''"

leq_def3_Nat [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat). (suc'(m) <='' suc'(X_n)) = (m <='' X_n)"

geq_def_Nat [rule_format] :
"ALL (m :: X_Nat). ALL (X_n :: X_Nat). (m >='' X_n) = (X_n <='' m)"

less_def_Nat [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat). (m <'' X_n) = (m <='' X_n & ~ m = X_n)"

greater_def_Nat [rule_format] :
"ALL (m :: X_Nat). ALL (X_n :: X_Nat). (m >'' X_n) = (X_n <'' m)"

even_0_Nat [rule_format] : "even''(0'')"

even_suc_Nat [rule_format] :
"ALL (m :: X_Nat). even''(suc'(m)) = odd''(m)"

odd_def_Nat [rule_format] :
"ALL (m :: X_Nat). odd''(m) = (~ even''(m))"

factorial_0 [rule_format] : "0'' !' = 1''"

factorial_suc [rule_format] :
"ALL (X_n :: X_Nat). suc'(X_n) !' = suc'(X_n) *'' X_n !'"

add_0_Nat [rule_format] : "ALL (m :: X_Nat). 0'' +'' m = m"

add_suc_Nat [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat). suc'(X_n) +'' m = suc'(X_n +'' m)"

mult_0_Nat [rule_format] : "ALL (m :: X_Nat). 0'' *'' m = 0''"

mult_suc_Nat [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat). suc'(X_n) *'' m = (X_n *'' m) +'' m"

power_0_Nat [rule_format] : "ALL (m :: X_Nat). m ^'' 0'' = 1''"

power_suc_Nat [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat). m ^'' suc'(X_n) = m *'' (m ^'' X_n)"

min_def_Nat [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat).
 min''(m, X_n) = (if m <='' X_n then m else X_n)"

max_def_Nat [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat).
 max''(m, X_n) = (if m <='' X_n then X_n else m)"

subTotal_def1_Nat [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat). m >'' X_n --> X_n -! m = 0''"

subTotal_def2_Nat [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat).
 m <='' X_n --> makePartial (X_n -! m) = X_n -? m"

sub_dom_Nat [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat). defOp (m -? X_n) = (m >='' X_n)"

sub_def_Nat [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat).
 ALL (r :: X_Nat). m -? X_n = makePartial r = (m = r +'' X_n)"

divide_dom_Nat [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat).
 defOp (m /?'' X_n) = (~ X_n = 0'' & m mod'' X_n = makePartial 0'')"

divide_0_Nat [rule_format] :
"ALL (m :: X_Nat). ~ defOp (m /?'' 0'')"

divide_Pos_Nat [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat).
 ALL (r :: X_Nat).
 X_n >'' 0'' --> m /?'' X_n = makePartial r = (m = r *'' X_n)"

div_dom_Nat [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat). defOp (m div'' X_n) = (~ X_n = 0'')"

div_Nat [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat).
 ALL (r :: X_Nat).
 m div'' X_n = makePartial r =
 (EX (s :: X_Nat). m = (X_n *'' r) +'' s & s <'' X_n)"

mod_dom_Nat [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat). defOp (m mod'' X_n) = (~ X_n = 0'')"

mod_Nat [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat).
 ALL (s :: X_Nat).
 m mod'' X_n = makePartial s =
 (EX (r :: X_Nat). m = (X_n *'' r) +'' s & s <'' X_n)"

distr1_Nat [rule_format] :
"ALL (r :: X_Nat).
 ALL (s :: X_Nat).
 ALL (t :: X_Nat). (r +'' s) *'' t = (r *'' t) +'' (s *'' t)"

distr2_Nat [rule_format] :
"ALL (r :: X_Nat).
 ALL (s :: X_Nat).
 ALL (t :: X_Nat). t *'' (r +'' s) = (t *'' r) +'' (t *'' s)"

Pos_def [rule_format] :
"ALL (p :: X_Nat).
 defOp ((X_gn_proj :: X_Nat => Pos partial) p) = (p >'' 0'')"

X1_as_Pos_def [rule_format] : "1_3 = suc''(0'')"

min_0 [rule_format] : "ALL (m :: X_Nat). min''(m, 0'') = 0''"

div_mod_Nat [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat).
 ~ X_n = 0'' -->
 makePartial m =
 restrictOp
 (makePartial
  ((makeTotal (m div'' X_n) *'' X_n) +'' makeTotal (m mod'' X_n)))
 (defOp (m div'' X_n) & defOp (m mod'' X_n))"

power_Nat [rule_format] :
"ALL (m :: X_Nat).
 ALL (r :: X_Nat).
 ALL (s :: X_Nat). m ^'' (r +'' s) = (m ^'' r) *'' (m ^'' s)"

ga_selector_ord [rule_format] :
"ALL (XX1 :: X_Nat).
 restrictOp (makePartial (ord'(makeTotal (chr(XX1)))))
 (defOp (chr(XX1))) =
 makePartial XX1"

chr_dom [rule_format] :
"ALL (X_n :: X_Nat).
 defOp (chr(X_n)) = (X_n <='' 2'' @@ (5'' @@ 5''))"

chr_ord_inverse [rule_format] :
"ALL (c :: Char). chr(ord'(c)) = makePartial c"

slash_000 [rule_format] : "makePartial '\\000' = chr(0'')"

slash_001 [rule_format] :
"makePartial '\\001' = chr((X_gn_inj :: Pos => X_Nat) 1_3)"

slash_002 [rule_format] : "makePartial '\\002' = chr(2'')"

slash_003 [rule_format] : "makePartial '\\003' = chr(3'')"

slash_004 [rule_format] : "makePartial '\\004' = chr(4'')"

slash_005 [rule_format] : "makePartial '\\005' = chr(5'')"

slash_006 [rule_format] : "makePartial '\\006' = chr(6'')"

slash_007 [rule_format] : "makePartial '\\007' = chr(7'')"

slash_008 [rule_format] : "makePartial '\\008' = chr(8'')"

slash_009 [rule_format] : "makePartial '\\009' = chr(9'')"

slash_010 [rule_format] :
"makePartial '\\010' = chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ 0'')"

slash_011 [rule_format] :
"makePartial '\\011' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@
     (X_gn_inj :: Pos => X_Nat) 1_3)"

slash_012 [rule_format] :
"makePartial '\\012' = chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ 2'')"

slash_013 [rule_format] :
"makePartial '\\013' = chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ 3'')"

slash_014 [rule_format] :
"makePartial '\\014' = chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ 4'')"

slash_015 [rule_format] :
"makePartial '\\015' = chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ 5'')"

slash_016 [rule_format] :
"makePartial '\\016' = chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ 6'')"

slash_017 [rule_format] :
"makePartial '\\017' = chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ 7'')"

slash_018 [rule_format] :
"makePartial '\\018' = chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ 8'')"

slash_019 [rule_format] :
"makePartial '\\019' = chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ 9'')"

slash_020 [rule_format] : "makePartial '\\020' = chr(2'' @@ 0'')"

slash_021 [rule_format] :
"makePartial '\\021' = chr(2'' @@ (X_gn_inj :: Pos => X_Nat) 1_3)"

slash_022 [rule_format] : "makePartial '\\022' = chr(2'' @@ 2'')"

slash_023 [rule_format] : "makePartial '\\023' = chr(2'' @@ 3'')"

slash_024 [rule_format] : "makePartial '\\024' = chr(2'' @@ 4'')"

slash_025 [rule_format] : "makePartial '\\025' = chr(2'' @@ 5'')"

slash_026 [rule_format] : "makePartial '\\026' = chr(2'' @@ 6'')"

slash_027 [rule_format] : "makePartial '\\027' = chr(2'' @@ 7'')"

slash_028 [rule_format] : "makePartial '\\028' = chr(2'' @@ 8'')"

slash_029 [rule_format] : "makePartial '\\029' = chr(2'' @@ 9'')"

slash_030 [rule_format] : "makePartial '\\030' = chr(3'' @@ 0'')"

slash_031 [rule_format] :
"makePartial '\\031' = chr(3'' @@ (X_gn_inj :: Pos => X_Nat) 1_3)"

slash_032 [rule_format] : "makePartial '\\032' = chr(3'' @@ 2'')"

slash_033 [rule_format] : "makePartial '\\033' = chr(3'' @@ 3'')"

slash_034 [rule_format] : "makePartial '\\034' = chr(3'' @@ 4'')"

slash_035 [rule_format] : "makePartial '\\035' = chr(3'' @@ 5'')"

slash_036 [rule_format] : "makePartial '\\036' = chr(3'' @@ 6'')"

slash_037 [rule_format] : "makePartial '\\037' = chr(3'' @@ 7'')"

slash_038 [rule_format] : "makePartial '\\038' = chr(3'' @@ 8'')"

slash_039 [rule_format] : "makePartial '\\039' = chr(3'' @@ 9'')"

slash_040 [rule_format] : "makePartial '\\040' = chr(4'' @@ 0'')"

slash_041 [rule_format] :
"makePartial '\\041' = chr(4'' @@ (X_gn_inj :: Pos => X_Nat) 1_3)"

slash_042 [rule_format] : "makePartial '\\042' = chr(4'' @@ 2'')"

slash_043 [rule_format] : "makePartial '\\043' = chr(4'' @@ 3'')"

slash_044 [rule_format] : "makePartial '\\044' = chr(4'' @@ 4'')"

slash_045 [rule_format] : "makePartial '\\045' = chr(4'' @@ 5'')"

slash_046 [rule_format] : "makePartial '\\046' = chr(4'' @@ 6'')"

slash_047 [rule_format] : "makePartial '\\047' = chr(4'' @@ 7'')"

slash_048 [rule_format] : "makePartial '\\048' = chr(4'' @@ 8'')"

slash_049 [rule_format] : "makePartial '\\049' = chr(4'' @@ 9'')"

slash_050 [rule_format] : "makePartial '\\050' = chr(5'' @@ 0'')"

slash_051 [rule_format] :
"makePartial '\\051' = chr(5'' @@ (X_gn_inj :: Pos => X_Nat) 1_3)"

slash_052 [rule_format] : "makePartial '\\052' = chr(5'' @@ 2'')"

slash_053 [rule_format] : "makePartial '\\053' = chr(5'' @@ 3'')"

slash_054 [rule_format] : "makePartial '\\054' = chr(5'' @@ 4'')"

slash_055 [rule_format] : "makePartial '\\055' = chr(5'' @@ 5'')"

slash_056 [rule_format] : "makePartial '\\056' = chr(5'' @@ 6'')"

slash_057 [rule_format] : "makePartial '\\057' = chr(5'' @@ 7'')"

slash_058 [rule_format] : "makePartial '\\058' = chr(5'' @@ 8'')"

slash_059 [rule_format] : "makePartial '\\059' = chr(5'' @@ 9'')"

slash_060 [rule_format] : "makePartial '\\060' = chr(6'' @@ 0'')"

slash_061 [rule_format] :
"makePartial '\\061' = chr(6'' @@ (X_gn_inj :: Pos => X_Nat) 1_3)"

slash_062 [rule_format] : "makePartial '\\062' = chr(6'' @@ 2'')"

slash_063 [rule_format] : "makePartial '\\063' = chr(6'' @@ 3'')"

slash_064 [rule_format] : "makePartial '\\064' = chr(6'' @@ 4'')"

slash_065 [rule_format] : "makePartial '\\065' = chr(6'' @@ 5'')"

slash_066 [rule_format] : "makePartial '\\066' = chr(6'' @@ 6'')"

slash_067 [rule_format] : "makePartial '\\067' = chr(6'' @@ 7'')"

slash_068 [rule_format] : "makePartial '\\068' = chr(6'' @@ 8'')"

slash_069 [rule_format] : "makePartial '\\069' = chr(6'' @@ 9'')"

slash_070 [rule_format] : "makePartial '\\070' = chr(7'' @@ 0'')"

slash_071 [rule_format] :
"makePartial '\\071' = chr(7'' @@ (X_gn_inj :: Pos => X_Nat) 1_3)"

slash_072 [rule_format] : "makePartial '\\072' = chr(7'' @@ 2'')"

slash_073 [rule_format] : "makePartial '\\073' = chr(7'' @@ 3'')"

slash_074 [rule_format] : "makePartial '\\074' = chr(7'' @@ 4'')"

slash_075 [rule_format] : "makePartial '\\075' = chr(7'' @@ 5'')"

slash_076 [rule_format] : "makePartial '\\076' = chr(7'' @@ 6'')"

slash_077 [rule_format] : "makePartial '\\077' = chr(7'' @@ 7'')"

slash_078 [rule_format] : "makePartial '\\078' = chr(7'' @@ 8'')"

slash_079 [rule_format] : "makePartial '\\079' = chr(7'' @@ 9'')"

slash_080 [rule_format] : "makePartial '\\080' = chr(8'' @@ 0'')"

slash_081 [rule_format] :
"makePartial '\\081' = chr(8'' @@ (X_gn_inj :: Pos => X_Nat) 1_3)"

slash_082 [rule_format] : "makePartial '\\082' = chr(8'' @@ 2'')"

slash_083 [rule_format] : "makePartial '\\083' = chr(8'' @@ 3'')"

slash_084 [rule_format] : "makePartial '\\084' = chr(8'' @@ 4'')"

slash_085 [rule_format] : "makePartial '\\085' = chr(8'' @@ 5'')"

slash_086 [rule_format] : "makePartial '\\086' = chr(8'' @@ 6'')"

slash_087 [rule_format] : "makePartial '\\087' = chr(8'' @@ 7'')"

slash_088 [rule_format] : "makePartial '\\088' = chr(8'' @@ 8'')"

slash_089 [rule_format] : "makePartial '\\089' = chr(8'' @@ 9'')"

slash_090 [rule_format] : "makePartial '\\090' = chr(9'' @@ 0'')"

slash_091 [rule_format] :
"makePartial '\\091' = chr(9'' @@ (X_gn_inj :: Pos => X_Nat) 1_3)"

slash_092 [rule_format] : "makePartial '\\092' = chr(9'' @@ 2'')"

slash_093 [rule_format] : "makePartial '\\093' = chr(9'' @@ 3'')"

slash_094 [rule_format] : "makePartial '\\094' = chr(9'' @@ 4'')"

slash_095 [rule_format] : "makePartial '\\095' = chr(9'' @@ 5'')"

slash_096 [rule_format] : "makePartial '\\096' = chr(9'' @@ 6'')"

slash_097 [rule_format] : "makePartial '\\097' = chr(9'' @@ 7'')"

slash_098 [rule_format] : "makePartial '\\098' = chr(9'' @@ 8'')"

slash_099 [rule_format] : "makePartial '\\099' = chr(9'' @@ 9'')"

slash_100 [rule_format] :
"makePartial '\\100' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (0'' @@ 0''))"

slash_101 [rule_format] :
"makePartial '\\101' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@
     (0'' @@ (X_gn_inj :: Pos => X_Nat) 1_3))"

slash_102 [rule_format] :
"makePartial '\\102' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (0'' @@ 2''))"

slash_103 [rule_format] :
"makePartial '\\103' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (0'' @@ 3''))"

slash_104 [rule_format] :
"makePartial '\\104' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (0'' @@ 4''))"

slash_105 [rule_format] :
"makePartial '\\105' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (0'' @@ 5''))"

slash_106 [rule_format] :
"makePartial '\\106' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (0'' @@ 6''))"

slash_107 [rule_format] :
"makePartial '\\107' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (0'' @@ 7''))"

slash_108 [rule_format] :
"makePartial '\\108' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (0'' @@ 8''))"

slash_109 [rule_format] :
"makePartial '\\109' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (0'' @@ 9''))"

slash_110 [rule_format] :
"makePartial '\\110' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@
     ((X_gn_inj :: Pos => X_Nat) 1_3 @@ 0''))"

slash_111 [rule_format] :
"makePartial '\\111' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@
     ((X_gn_inj :: Pos => X_Nat) 1_3 @@
      (X_gn_inj :: Pos => X_Nat) 1_3))"

slash_112 [rule_format] :
"makePartial '\\112' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@
     ((X_gn_inj :: Pos => X_Nat) 1_3 @@ 2''))"

slash_113 [rule_format] :
"makePartial '\\113' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@
     ((X_gn_inj :: Pos => X_Nat) 1_3 @@ 3''))"

slash_114 [rule_format] :
"makePartial '\\114' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@
     ((X_gn_inj :: Pos => X_Nat) 1_3 @@ 4''))"

slash_115 [rule_format] :
"makePartial '\\115' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@
     ((X_gn_inj :: Pos => X_Nat) 1_3 @@ 5''))"

slash_116 [rule_format] :
"makePartial '\\116' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@
     ((X_gn_inj :: Pos => X_Nat) 1_3 @@ 6''))"

slash_117 [rule_format] :
"makePartial '\\117' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@
     ((X_gn_inj :: Pos => X_Nat) 1_3 @@ 7''))"

slash_118 [rule_format] :
"makePartial '\\118' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@
     ((X_gn_inj :: Pos => X_Nat) 1_3 @@ 8''))"

slash_119 [rule_format] :
"makePartial '\\119' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@
     ((X_gn_inj :: Pos => X_Nat) 1_3 @@ 9''))"

slash_120 [rule_format] :
"makePartial '\\120' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (2'' @@ 0''))"

slash_121 [rule_format] :
"makePartial '\\121' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@
     (2'' @@ (X_gn_inj :: Pos => X_Nat) 1_3))"

slash_122 [rule_format] :
"makePartial '\\122' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (2'' @@ 2''))"

slash_123 [rule_format] :
"makePartial '\\123' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (2'' @@ 3''))"

slash_124 [rule_format] :
"makePartial '\\124' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (2'' @@ 4''))"

slash_125 [rule_format] :
"makePartial '\\125' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (2'' @@ 5''))"

slash_126 [rule_format] :
"makePartial '\\126' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (2'' @@ 6''))"

slash_127 [rule_format] :
"makePartial '\\127' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (2'' @@ 7''))"

slash_128 [rule_format] :
"makePartial '\\128' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (2'' @@ 8''))"

slash_129 [rule_format] :
"makePartial '\\129' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (2'' @@ 9''))"

slash_130 [rule_format] :
"makePartial '\\130' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (3'' @@ 0''))"

slash_131 [rule_format] :
"makePartial '\\131' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@
     (3'' @@ (X_gn_inj :: Pos => X_Nat) 1_3))"

slash_132 [rule_format] :
"makePartial '\\132' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (3'' @@ 2''))"

slash_133 [rule_format] :
"makePartial '\\133' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (3'' @@ 3''))"

slash_134 [rule_format] :
"makePartial '\\134' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (3'' @@ 4''))"

slash_135 [rule_format] :
"makePartial '\\135' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (3'' @@ 5''))"

slash_136 [rule_format] :
"makePartial '\\136' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (3'' @@ 6''))"

slash_137 [rule_format] :
"makePartial '\\137' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (3'' @@ 7''))"

slash_138 [rule_format] :
"makePartial '\\138' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (3'' @@ 8''))"

slash_139 [rule_format] :
"makePartial '\\139' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (3'' @@ 9''))"

slash_140 [rule_format] :
"makePartial '\\140' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (4'' @@ 0''))"

slash_141 [rule_format] :
"makePartial '\\141' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@
     (4'' @@ (X_gn_inj :: Pos => X_Nat) 1_3))"

slash_142 [rule_format] :
"makePartial '\\142' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (4'' @@ 2''))"

slash_143 [rule_format] :
"makePartial '\\143' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (4'' @@ 3''))"

slash_144 [rule_format] :
"makePartial '\\144' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (4'' @@ 4''))"

slash_145 [rule_format] :
"makePartial '\\145' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (4'' @@ 5''))"

slash_146 [rule_format] :
"makePartial '\\146' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (4'' @@ 6''))"

slash_147 [rule_format] :
"makePartial '\\147' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (4'' @@ 7''))"

slash_148 [rule_format] :
"makePartial '\\148' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (4'' @@ 8''))"

slash_149 [rule_format] :
"makePartial '\\149' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (4'' @@ 9''))"

slash_150 [rule_format] :
"makePartial '\\150' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (5'' @@ 0''))"

slash_151 [rule_format] :
"makePartial '\\151' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@
     (5'' @@ (X_gn_inj :: Pos => X_Nat) 1_3))"

slash_152 [rule_format] :
"makePartial '\\152' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (5'' @@ 2''))"

slash_153 [rule_format] :
"makePartial '\\153' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (5'' @@ 3''))"

slash_154 [rule_format] :
"makePartial '\\154' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (5'' @@ 4''))"

slash_155 [rule_format] :
"makePartial '\\155' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (5'' @@ 5''))"

slash_156 [rule_format] :
"makePartial '\\156' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (5'' @@ 6''))"

slash_157 [rule_format] :
"makePartial '\\157' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (5'' @@ 7''))"

slash_158 [rule_format] :
"makePartial '\\158' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (5'' @@ 8''))"

slash_159 [rule_format] :
"makePartial '\\159' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (5'' @@ 9''))"

slash_160 [rule_format] :
"makePartial '\\160' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (6'' @@ 0''))"

slash_161 [rule_format] :
"makePartial '\\161' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@
     (6'' @@ (X_gn_inj :: Pos => X_Nat) 1_3))"

slash_162 [rule_format] :
"makePartial '\\162' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (6'' @@ 2''))"

slash_163 [rule_format] :
"makePartial '\\163' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (6'' @@ 3''))"

slash_164 [rule_format] :
"makePartial '\\164' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (6'' @@ 4''))"

slash_165 [rule_format] :
"makePartial '\\165' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (6'' @@ 5''))"

slash_166 [rule_format] :
"makePartial '\\166' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (6'' @@ 6''))"

slash_167 [rule_format] :
"makePartial '\\167' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (6'' @@ 7''))"

slash_168 [rule_format] :
"makePartial '\\168' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (6'' @@ 8''))"

slash_169 [rule_format] :
"makePartial '\\169' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (6'' @@ 9''))"

slash_170 [rule_format] :
"makePartial '\\170' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (7'' @@ 0''))"

slash_171 [rule_format] :
"makePartial '\\171' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@
     (7'' @@ (X_gn_inj :: Pos => X_Nat) 1_3))"

slash_172 [rule_format] :
"makePartial '\\172' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (7'' @@ 2''))"

slash_173 [rule_format] :
"makePartial '\\173' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (7'' @@ 3''))"

slash_174 [rule_format] :
"makePartial '\\174' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (7'' @@ 4''))"

slash_175 [rule_format] :
"makePartial '\\175' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (7'' @@ 5''))"

slash_176 [rule_format] :
"makePartial '\\176' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (7'' @@ 6''))"

slash_177 [rule_format] :
"makePartial '\\177' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (7'' @@ 7''))"

slash_178 [rule_format] :
"makePartial '\\178' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (7'' @@ 8''))"

slash_179 [rule_format] :
"makePartial '\\179' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (7'' @@ 9''))"

slash_180 [rule_format] :
"makePartial '\\180' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (8'' @@ 0''))"

slash_181 [rule_format] :
"makePartial '\\181' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@
     (8'' @@ (X_gn_inj :: Pos => X_Nat) 1_3))"

slash_182 [rule_format] :
"makePartial '\\182' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (8'' @@ 2''))"

slash_183 [rule_format] :
"makePartial '\\183' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (8'' @@ 3''))"

slash_184 [rule_format] :
"makePartial '\\184' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (8'' @@ 4''))"

slash_185 [rule_format] :
"makePartial '\\185' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (8'' @@ 5''))"

slash_186 [rule_format] :
"makePartial '\\186' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (8'' @@ 6''))"

slash_187 [rule_format] :
"makePartial '\\187' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (8'' @@ 7''))"

slash_188 [rule_format] :
"makePartial '\\188' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (8'' @@ 8''))"

slash_189 [rule_format] :
"makePartial '\\189' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (8'' @@ 9''))"

slash_190 [rule_format] :
"makePartial '\\190' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (9'' @@ 0''))"

slash_191 [rule_format] :
"makePartial '\\191' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@
     (9'' @@ (X_gn_inj :: Pos => X_Nat) 1_3))"

slash_192 [rule_format] :
"makePartial '\\192' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (9'' @@ 2''))"

slash_193 [rule_format] :
"makePartial '\\193' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (9'' @@ 3''))"

slash_194 [rule_format] :
"makePartial '\\194' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (9'' @@ 4''))"

slash_195 [rule_format] :
"makePartial '\\195' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (9'' @@ 5''))"

slash_196 [rule_format] :
"makePartial '\\196' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (9'' @@ 6''))"

slash_197 [rule_format] :
"makePartial '\\197' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (9'' @@ 7''))"

slash_198 [rule_format] :
"makePartial '\\198' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (9'' @@ 8''))"

slash_199 [rule_format] :
"makePartial '\\199' =
 chr((X_gn_inj :: Pos => X_Nat) 1_3 @@ (9'' @@ 9''))"

slash_200 [rule_format] :
"makePartial '\\200' = chr(2'' @@ (0'' @@ 0''))"

slash_201 [rule_format] :
"makePartial '\\201' =
 chr(2'' @@ (0'' @@ (X_gn_inj :: Pos => X_Nat) 1_3))"

slash_202 [rule_format] :
"makePartial '\\202' = chr(2'' @@ (0'' @@ 2''))"

slash_203 [rule_format] :
"makePartial '\\203' = chr(2'' @@ (0'' @@ 3''))"

slash_204 [rule_format] :
"makePartial '\\204' = chr(2'' @@ (0'' @@ 4''))"

slash_205 [rule_format] :
"makePartial '\\205' = chr(2'' @@ (0'' @@ 5''))"

slash_206 [rule_format] :
"makePartial '\\206' = chr(2'' @@ (0'' @@ 6''))"

slash_207 [rule_format] :
"makePartial '\\207' = chr(2'' @@ (0'' @@ 7''))"

slash_208 [rule_format] :
"makePartial '\\208' = chr(2'' @@ (0'' @@ 8''))"

slash_209 [rule_format] :
"makePartial '\\209' = chr(2'' @@ (0'' @@ 9''))"

slash_210 [rule_format] :
"makePartial '\\210' =
 chr(2'' @@ ((X_gn_inj :: Pos => X_Nat) 1_3 @@ 0''))"

slash_211 [rule_format] :
"makePartial '\\211' =
 chr(2'' @@
     ((X_gn_inj :: Pos => X_Nat) 1_3 @@
      (X_gn_inj :: Pos => X_Nat) 1_3))"

slash_212 [rule_format] :
"makePartial '\\212' =
 chr(2'' @@ ((X_gn_inj :: Pos => X_Nat) 1_3 @@ 2''))"

slash_213 [rule_format] :
"makePartial '\\213' =
 chr(2'' @@ ((X_gn_inj :: Pos => X_Nat) 1_3 @@ 3''))"

slash_214 [rule_format] :
"makePartial '\\214' =
 chr(2'' @@ ((X_gn_inj :: Pos => X_Nat) 1_3 @@ 4''))"

slash_215 [rule_format] :
"makePartial '\\215' =
 chr(2'' @@ ((X_gn_inj :: Pos => X_Nat) 1_3 @@ 5''))"

slash_216 [rule_format] :
"makePartial '\\216' =
 chr(2'' @@ ((X_gn_inj :: Pos => X_Nat) 1_3 @@ 6''))"

slash_217 [rule_format] :
"makePartial '\\217' =
 chr(2'' @@ ((X_gn_inj :: Pos => X_Nat) 1_3 @@ 7''))"

slash_218 [rule_format] :
"makePartial '\\218' =
 chr(2'' @@ ((X_gn_inj :: Pos => X_Nat) 1_3 @@ 8''))"

slash_219 [rule_format] :
"makePartial '\\219' =
 chr(2'' @@ ((X_gn_inj :: Pos => X_Nat) 1_3 @@ 9''))"

slash_220 [rule_format] :
"makePartial '\\220' = chr(2'' @@ (2'' @@ 0''))"

slash_221 [rule_format] :
"makePartial '\\221' =
 chr(2'' @@ (2'' @@ (X_gn_inj :: Pos => X_Nat) 1_3))"

slash_222 [rule_format] :
"makePartial '\\222' = chr(2'' @@ (2'' @@ 2''))"

slash_223 [rule_format] :
"makePartial '\\223' = chr(2'' @@ (2'' @@ 3''))"

slash_224 [rule_format] :
"makePartial '\\224' = chr(2'' @@ (2'' @@ 4''))"

slash_225 [rule_format] :
"makePartial '\\225' = chr(2'' @@ (2'' @@ 5''))"

slash_226 [rule_format] :
"makePartial '\\226' = chr(2'' @@ (2'' @@ 6''))"

slash_227 [rule_format] :
"makePartial '\\227' = chr(2'' @@ (2'' @@ 7''))"

slash_228 [rule_format] :
"makePartial '\\228' = chr(2'' @@ (2'' @@ 8''))"

slash_229 [rule_format] :
"makePartial '\\229' = chr(2'' @@ (2'' @@ 9''))"

slash_230 [rule_format] :
"makePartial '\\230' = chr(2'' @@ (3'' @@ 0''))"

slash_231 [rule_format] :
"makePartial '\\231' =
 chr(2'' @@ (3'' @@ (X_gn_inj :: Pos => X_Nat) 1_3))"

slash_232 [rule_format] :
"makePartial '\\232' = chr(2'' @@ (3'' @@ 2''))"

slash_233 [rule_format] :
"makePartial '\\233' = chr(2'' @@ (3'' @@ 3''))"

slash_234 [rule_format] :
"makePartial '\\234' = chr(2'' @@ (3'' @@ 4''))"

slash_235 [rule_format] :
"makePartial '\\235' = chr(2'' @@ (3'' @@ 5''))"

slash_236 [rule_format] :
"makePartial '\\236' = chr(2'' @@ (3'' @@ 6''))"

slash_237 [rule_format] :
"makePartial '\\237' = chr(2'' @@ (3'' @@ 7''))"

slash_238 [rule_format] :
"makePartial '\\238' = chr(2'' @@ (3'' @@ 8''))"

slash_239 [rule_format] :
"makePartial '\\239' = chr(2'' @@ (3'' @@ 9''))"

slash_240 [rule_format] :
"makePartial '\\240' = chr(2'' @@ (4'' @@ 0''))"

slash_241 [rule_format] :
"makePartial '\\241' =
 chr(2'' @@ (4'' @@ (X_gn_inj :: Pos => X_Nat) 1_3))"

slash_242 [rule_format] :
"makePartial '\\242' = chr(2'' @@ (4'' @@ 2''))"

slash_243 [rule_format] :
"makePartial '\\243' = chr(2'' @@ (4'' @@ 3''))"

slash_244 [rule_format] :
"makePartial '\\244' = chr(2'' @@ (4'' @@ 4''))"

slash_245 [rule_format] :
"makePartial '\\245' = chr(2'' @@ (4'' @@ 5''))"

slash_246 [rule_format] :
"makePartial '\\246' = chr(2'' @@ (4'' @@ 6''))"

slash_247 [rule_format] :
"makePartial '\\247' = chr(2'' @@ (4'' @@ 7''))"

slash_248 [rule_format] :
"makePartial '\\248' = chr(2'' @@ (4'' @@ 8''))"

slash_249 [rule_format] :
"makePartial '\\249' = chr(2'' @@ (4'' @@ 9''))"

slash_250 [rule_format] :
"makePartial '\\250' = chr(2'' @@ (5'' @@ 0''))"

slash_251 [rule_format] :
"makePartial '\\251' =
 chr(2'' @@ (5'' @@ (X_gn_inj :: Pos => X_Nat) 1_3))"

slash_252 [rule_format] :
"makePartial '\\252' = chr(2'' @@ (5'' @@ 2''))"

slash_253 [rule_format] :
"makePartial '\\253' = chr(2'' @@ (5'' @@ 3''))"

slash_254 [rule_format] :
"makePartial '\\254' = chr(2'' @@ (5'' @@ 4''))"

slash_255 [rule_format] :
"makePartial '\\255' = chr(2'' @@ (5'' @@ 5''))"

printable_32 [rule_format] : "' ' = '\\032'"

printable_33 [rule_format] : "'!' = '\\033'"

printable_34 [rule_format] : "'\\\"' = '\\034'"

printable_35 [rule_format] : "'#' = '\\035'"

printable_36 [rule_format] : "'$' = '\\036'"

printable_37 [rule_format] : "'%' = '\\037'"

printable_38 [rule_format] : "'&' = '\\038'"

printable_39 [rule_format] : "'\\'' = '\\039'"

printable_40 [rule_format] : "'(' = '\\040'"

printable_41 [rule_format] : "')' = '\\041'"

printable_42 [rule_format] : "'*' = '\\042'"

printable_43 [rule_format] : "'+' = '\\043'"

printable_44 [rule_format] : "',' = '\\044'"

printable_45 [rule_format] : "'-' = '\\045'"

printable_46 [rule_format] : "'.' = '\\046'"

printable_47 [rule_format] : "'/' = '\\047'"

printable_48 [rule_format] : "'0' = '\\048'"

printable_49 [rule_format] : "'1' = '\\049'"

printable_50 [rule_format] : "'2' = '\\050'"

printable_51 [rule_format] : "'3' = '\\051'"

printable_52 [rule_format] : "'4' = '\\052'"

printable_53 [rule_format] : "'5' = '\\053'"

printable_54 [rule_format] : "'6' = '\\054'"

printable_55 [rule_format] : "'7' = '\\055'"

printable_56 [rule_format] : "'8' = '\\056'"

printable_57 [rule_format] : "'9' = '\\057'"

printable_58 [rule_format] : "':' = '\\058'"

printable_59 [rule_format] : "';' = '\\059'"

printable_60 [rule_format] : "'<' = '\\060'"

printable_61 [rule_format] : "'=' = '\\061'"

printable_62 [rule_format] : "'>' = '\\062'"

printable_63 [rule_format] : "'?' = '\\063'"

printable_64 [rule_format] : "'@' = '\\064'"

printable_65 [rule_format] : "'A' = '\\065'"

printable_66 [rule_format] : "'B' = '\\066'"

printable_67 [rule_format] : "'C' = '\\067'"

printable_68 [rule_format] : "'D' = '\\068'"

printable_69 [rule_format] : "'E' = '\\069'"

printable_70 [rule_format] : "'F' = '\\070'"

printable_71 [rule_format] : "'G' = '\\071'"

printable_72 [rule_format] : "'H' = '\\072'"

printable_73 [rule_format] : "'I' = '\\073'"

printable_74 [rule_format] : "'J' = '\\074'"

printable_75 [rule_format] : "'K' = '\\075'"

printable_76 [rule_format] : "'L' = '\\076'"

printable_77 [rule_format] : "'M' = '\\077'"

printable_78 [rule_format] : "'N' = '\\078'"

printable_79 [rule_format] : "'O' = '\\079'"

printable_80 [rule_format] : "'P' = '\\080'"

printable_81 [rule_format] : "'Q' = '\\081'"

printable_82 [rule_format] : "'R' = '\\082'"

printable_83 [rule_format] : "'S' = '\\083'"

printable_84 [rule_format] : "'T' = '\\084'"

printable_85 [rule_format] : "'U' = '\\085'"

printable_86 [rule_format] : "'V' = '\\086'"

printable_87 [rule_format] : "'W' = '\\087'"

printable_88 [rule_format] : "'X' = '\\088'"

printable_89 [rule_format] : "'Y' = '\\089'"

printable_90 [rule_format] : "'Z' = '\\090'"

printable_91 [rule_format] : "'[' = '\\091'"

printable_92 [rule_format] : "'\\\\' = '\\092'"

printable_93 [rule_format] : "']' = '\\093'"

printable_94 [rule_format] : "'^' = '\\094'"

printable_95 [rule_format] : "'_' = '\\095'"

printable_96 [rule_format] : "'`' = '\\096'"

printable_97 [rule_format] : "'a' = '\\097'"

printable_98 [rule_format] : "'b' = '\\098'"

printable_99 [rule_format] : "'c' = '\\099'"

printable_100 [rule_format] : "'d' = '\\100'"

printable_101 [rule_format] : "'e' = '\\101'"

printable_102 [rule_format] : "'f' = '\\102'"

printable_103 [rule_format] : "'g' = '\\103'"

printable_104 [rule_format] : "'h' = '\\104'"

printable_105 [rule_format] : "'i' = '\\105'"

printable_106 [rule_format] : "'j' = '\\106'"

printable_107 [rule_format] : "'k' = '\\107'"

printable_108 [rule_format] : "'l' = '\\108'"

printable_109 [rule_format] : "'m' = '\\109'"

printable_110 [rule_format] : "'n' = '\\110'"

printable_111 [rule_format] : "'o' = '\\111'"

printable_112 [rule_format] : "'p' = '\\112'"

printable_113 [rule_format] : "'q' = '\\113'"

printable_114 [rule_format] : "'r' = '\\114'"

printable_115 [rule_format] : "'s' = '\\115'"

printable_116 [rule_format] : "'t' = '\\116'"

printable_117 [rule_format] : "'u' = '\\117'"

printable_118 [rule_format] : "'v' = '\\118'"

printable_119 [rule_format] : "'w' = '\\119'"

printable_120 [rule_format] : "'x' = '\\120'"

printable_121 [rule_format] : "'y' = '\\121'"

printable_122 [rule_format] : "'z' = '\\122'"

printable_123 [rule_format] : "'{' = '\\123'"

printable_124 [rule_format] : "'|' = '\\124'"

printable_125 [rule_format] : "'}' = '\\125'"

printable_126 [rule_format] : "'~' = '\\126'"

printable_160 [rule_format] : "' ' = '\\160'"

printable_161 [rule_format] : "'¡' = '\\161'"

printable_162 [rule_format] : "'¢' = '\\162'"

printable_163 [rule_format] : "'£' = '\\163'"

printable_164 [rule_format] : "'¤' = '\\164'"

printable_165 [rule_format] : "'¥' = '\\165'"

printable_166 [rule_format] : "'¦' = '\\166'"

printable_167 [rule_format] : "'§' = '\\167'"

printable_168 [rule_format] : "'¨' = '\\168'"

printable_169 [rule_format] : "'©' = '\\169'"

printable_170 [rule_format] : "'ª' = '\\170'"

printable_171 [rule_format] : "'«' = '\\171'"

printable_172 [rule_format] : "'¬' = '\\172'"

printable_173 [rule_format] : "'­' = '\\173'"

printable_174 [rule_format] : "'®' = '\\174'"

printable_175 [rule_format] : "'¯' = '\\175'"

printable_176 [rule_format] : "'°' = '\\176'"

printable_177 [rule_format] : "'±' = '\\177'"

printable_178 [rule_format] : "'²' = '\\178'"

printable_179 [rule_format] : "'³' = '\\179'"

printable_180 [rule_format] : "'´' = '\\180'"

printable_181 [rule_format] : "'µ' = '\\181'"

printable_182 [rule_format] : "'¶' = '\\182'"

printable_183 [rule_format] : "'·' = '\\183'"

printable_184 [rule_format] : "'¸' = '\\184'"

printable_185 [rule_format] : "'¹' = '\\185'"

printable_186 [rule_format] : "'º' = '\\186'"

printable_187 [rule_format] : "'»' = '\\187'"

printable_188 [rule_format] : "'¼' = '\\188'"

printable_189 [rule_format] : "'½' = '\\189'"

printable_190 [rule_format] : "'¾' = '\\190'"

printable_191 [rule_format] : "'¿' = '\\191'"

printable_192 [rule_format] : "'À' = '\\192'"

printable_193 [rule_format] : "'Á' = '\\193'"

printable_194 [rule_format] : "'Â' = '\\194'"

printable_195 [rule_format] : "'Ã' = '\\195'"

printable_196 [rule_format] : "'Ä' = '\\196'"

printable_197 [rule_format] : "'Å' = '\\197'"

printable_198 [rule_format] : "'Æ' = '\\198'"

printable_199 [rule_format] : "'Ç' = '\\199'"

printable_200 [rule_format] : "'È' = '\\200'"

printable_201 [rule_format] : "'É' = '\\201'"

printable_202 [rule_format] : "'Ê' = '\\202'"

printable_203 [rule_format] : "'Ë' = '\\203'"

printable_204 [rule_format] : "'Ì' = '\\204'"

printable_205 [rule_format] : "'Í' = '\\205'"

printable_206 [rule_format] : "'Î' = '\\206'"

printable_207 [rule_format] : "'Ï' = '\\207'"

printable_208 [rule_format] : "'Ð' = '\\208'"

printable_209 [rule_format] : "'Ñ' = '\\209'"

printable_210 [rule_format] : "'Ò' = '\\210'"

printable_211 [rule_format] : "'Ó' = '\\211'"

printable_212 [rule_format] : "'Ô' = '\\212'"

printable_213 [rule_format] : "'Õ' = '\\213'"

printable_214 [rule_format] : "'Ö' = '\\214'"

printable_215 [rule_format] : "'×' = '\\215'"

printable_216 [rule_format] : "'Ø' = '\\216'"

printable_217 [rule_format] : "'Ù' = '\\217'"

printable_218 [rule_format] : "'Ú' = '\\218'"

printable_219 [rule_format] : "'Û' = '\\219'"

printable_220 [rule_format] : "'Ü' = '\\220'"

printable_221 [rule_format] : "'Ý' = '\\221'"

printable_222 [rule_format] : "'Þ' = '\\222'"

printable_223 [rule_format] : "'ß' = '\\223'"

printable_224 [rule_format] : "'à' = '\\224'"

printable_225 [rule_format] : "'á' = '\\225'"

printable_226 [rule_format] : "'â' = '\\226'"

printable_227 [rule_format] : "'ã' = '\\227'"

printable_228 [rule_format] : "'ä' = '\\228'"

printable_229 [rule_format] : "'å' = '\\229'"

printable_230 [rule_format] : "'æ' = '\\230'"

printable_231 [rule_format] : "'ç' = '\\231'"

printable_232 [rule_format] : "'è' = '\\232'"

printable_233 [rule_format] : "'é' = '\\233'"

printable_234 [rule_format] : "'ê' = '\\234'"

printable_235 [rule_format] : "'ë' = '\\235'"

printable_236 [rule_format] : "'ì' = '\\236'"

printable_237 [rule_format] : "'í' = '\\237'"

printable_238 [rule_format] : "'î' = '\\238'"

printable_239 [rule_format] : "'ï' = '\\239'"

printable_240 [rule_format] : "'ð' = '\\240'"

printable_241 [rule_format] : "'ñ' = '\\241'"

printable_242 [rule_format] : "'ò' = '\\242'"

printable_243 [rule_format] : "'ó' = '\\243'"

printable_244 [rule_format] : "'ô' = '\\244'"

printable_245 [rule_format] : "'õ' = '\\245'"

printable_246 [rule_format] : "'ö' = '\\246'"

printable_247 [rule_format] : "'÷' = '\\247'"

printable_248 [rule_format] : "'ø' = '\\248'"

printable_249 [rule_format] : "'ù' = '\\249'"

printable_250 [rule_format] : "'ú' = '\\250'"

printable_251 [rule_format] : "'û' = '\\251'"

printable_252 [rule_format] : "'ü' = '\\252'"

printable_253 [rule_format] : "'ý' = '\\253'"

printable_254 [rule_format] : "'þ' = '\\254'"

printable_255 [rule_format] : "'ÿ' = '\\255'"

isLetter_def [rule_format] :
"ALL (c :: Char).
 isLetter(c) =
 (ord'('A') <='' ord'(c) & ord'(c) <='' ord'('Z') |
  ord'('a') <='' ord'(c) & ord'(c) <='' ord'('z'))"

isDigit_def [rule_format] :
"ALL (c :: Char).
 isDigit(c) = (ord'('0') <='' ord'(c) & ord'(c) <='' ord'('9'))"

isPrintable_def [rule_format] :
"ALL (c :: Char).
 isPrintable(c) =
 (ord'(' ') <='' ord'(c) & ord'(c) <='' ord'('~') |
  ord'(' ') <='' ord'(c) & ord'(c) <='' ord'('ÿ'))"

slash_o000 [rule_format] : "'\\o000' = '\\000'"

slash_o001 [rule_format] : "'\\o001' = '\\001'"

slash_o002 [rule_format] : "'\\o002' = '\\002'"

slash_o003 [rule_format] : "'\\o003' = '\\003'"

slash_o004 [rule_format] : "'\\o004' = '\\004'"

slash_o005 [rule_format] : "'\\o005' = '\\005'"

slash_o006 [rule_format] : "'\\o006' = '\\006'"

slash_o007 [rule_format] : "'\\o007' = '\\007'"

slash_o010 [rule_format] : "'\\o010' = '\\008'"

slash_o011 [rule_format] : "'\\o011' = '\\009'"

slash_o012 [rule_format] : "'\\o012' = '\\010'"

slash_o013 [rule_format] : "'\\o013' = '\\011'"

slash_o014 [rule_format] : "'\\o014' = '\\012'"

slash_o015 [rule_format] : "'\\o015' = '\\013'"

slash_o016 [rule_format] : "'\\o016' = '\\014'"

slash_o017 [rule_format] : "'\\o017' = '\\015'"

slash_o020 [rule_format] : "'\\o020' = '\\016'"

slash_o021 [rule_format] : "'\\o021' = '\\017'"

slash_o022 [rule_format] : "'\\o022' = '\\018'"

slash_o023 [rule_format] : "'\\o023' = '\\019'"

slash_o024 [rule_format] : "'\\o024' = '\\020'"

slash_o025 [rule_format] : "'\\o025' = '\\021'"

slash_o026 [rule_format] : "'\\o026' = '\\022'"

slash_o027 [rule_format] : "'\\o027' = '\\023'"

slash_o030 [rule_format] : "'\\o030' = '\\024'"

slash_o031 [rule_format] : "'\\o031' = '\\025'"

slash_o032 [rule_format] : "'\\o032' = '\\026'"

slash_o033 [rule_format] : "'\\o033' = '\\027'"

slash_o034 [rule_format] : "'\\o034' = '\\028'"

slash_o035 [rule_format] : "'\\o035' = '\\029'"

slash_o036 [rule_format] : "'\\o036' = '\\030'"

slash_o037 [rule_format] : "'\\o037' = '\\031'"

slash_o040 [rule_format] : "'\\o040' = '\\032'"

slash_o041 [rule_format] : "'\\o041' = '\\033'"

slash_o042 [rule_format] : "'\\o042' = '\\034'"

slash_o043 [rule_format] : "'\\o043' = '\\035'"

slash_o044 [rule_format] : "'\\o044' = '\\036'"

slash_o045 [rule_format] : "'\\o045' = '\\037'"

slash_o046 [rule_format] : "'\\o046' = '\\038'"

slash_o047 [rule_format] : "'\\o047' = '\\039'"

slash_o050 [rule_format] : "'\\o050' = '\\040'"

slash_o051 [rule_format] : "'\\o051' = '\\041'"

slash_o052 [rule_format] : "'\\o052' = '\\042'"

slash_o053 [rule_format] : "'\\o053' = '\\043'"

slash_o054 [rule_format] : "'\\o054' = '\\044'"

slash_o055 [rule_format] : "'\\o055' = '\\045'"

slash_o056 [rule_format] : "'\\o056' = '\\046'"

slash_o057 [rule_format] : "'\\o057' = '\\047'"

slash_o060 [rule_format] : "'\\o060' = '\\048'"

slash_o061 [rule_format] : "'\\o061' = '\\049'"

slash_o062 [rule_format] : "'\\o062' = '\\050'"

slash_o063 [rule_format] : "'\\o063' = '\\051'"

slash_o064 [rule_format] : "'\\o064' = '\\052'"

slash_o065 [rule_format] : "'\\o065' = '\\053'"

slash_o066 [rule_format] : "'\\o066' = '\\054'"

slash_o067 [rule_format] : "'\\o067' = '\\055'"

slash_o070 [rule_format] : "'\\o070' = '\\056'"

slash_o071 [rule_format] : "'\\o071' = '\\057'"

slash_o072 [rule_format] : "'\\o072' = '\\058'"

slash_o073 [rule_format] : "'\\o073' = '\\059'"

slash_o074 [rule_format] : "'\\o074' = '\\060'"

slash_o075 [rule_format] : "'\\o075' = '\\061'"

slash_o076 [rule_format] : "'\\o076' = '\\062'"

slash_o077 [rule_format] : "'\\o077' = '\\063'"

slash_o100 [rule_format] : "'\\o100' = '\\064'"

slash_o101 [rule_format] : "'\\o101' = '\\065'"

slash_o102 [rule_format] : "'\\o102' = '\\066'"

slash_o103 [rule_format] : "'\\o103' = '\\067'"

slash_o104 [rule_format] : "'\\o104' = '\\068'"

slash_o105 [rule_format] : "'\\o105' = '\\069'"

slash_o106 [rule_format] : "'\\o106' = '\\070'"

slash_o107 [rule_format] : "'\\o107' = '\\071'"

slash_o110 [rule_format] : "'\\o110' = '\\072'"

slash_o111 [rule_format] : "'\\o111' = '\\073'"

slash_o112 [rule_format] : "'\\o112' = '\\074'"

slash_o113 [rule_format] : "'\\o113' = '\\075'"

slash_o114 [rule_format] : "'\\o114' = '\\076'"

slash_o115 [rule_format] : "'\\o115' = '\\077'"

slash_o116 [rule_format] : "'\\o116' = '\\078'"

slash_o117 [rule_format] : "'\\o117' = '\\079'"

slash_o120 [rule_format] : "'\\o120' = '\\080'"

slash_o121 [rule_format] : "'\\o121' = '\\081'"

slash_o122 [rule_format] : "'\\o122' = '\\082'"

slash_o123 [rule_format] : "'\\o123' = '\\083'"

slash_o124 [rule_format] : "'\\o124' = '\\084'"

slash_o125 [rule_format] : "'\\o125' = '\\085'"

slash_o126 [rule_format] : "'\\o126' = '\\086'"

slash_o127 [rule_format] : "'\\o127' = '\\087'"

slash_o130 [rule_format] : "'\\o130' = '\\088'"

slash_o131 [rule_format] : "'\\o131' = '\\089'"

slash_o132 [rule_format] : "'\\o132' = '\\090'"

slash_o133 [rule_format] : "'\\o133' = '\\091'"

slash_o134 [rule_format] : "'\\o134' = '\\092'"

slash_o135 [rule_format] : "'\\o135' = '\\093'"

slash_o136 [rule_format] : "'\\o136' = '\\094'"

slash_o137 [rule_format] : "'\\o137' = '\\095'"

slash_o140 [rule_format] : "'\\o140' = '\\096'"

slash_o141 [rule_format] : "'\\o141' = '\\097'"

slash_o142 [rule_format] : "'\\o142' = '\\098'"

slash_o143 [rule_format] : "'\\o143' = '\\099'"

slash_o144 [rule_format] : "'\\o144' = '\\100'"

slash_o145 [rule_format] : "'\\o145' = '\\101'"

slash_o146 [rule_format] : "'\\o146' = '\\102'"

slash_o147 [rule_format] : "'\\o147' = '\\103'"

slash_o150 [rule_format] : "'\\o150' = '\\104'"

slash_o151 [rule_format] : "'\\o151' = '\\105'"

slash_o152 [rule_format] : "'\\o152' = '\\106'"

slash_o153 [rule_format] : "'\\o153' = '\\107'"

slash_o154 [rule_format] : "'\\o154' = '\\108'"

slash_o155 [rule_format] : "'\\o155' = '\\109'"

slash_o156 [rule_format] : "'\\o156' = '\\110'"

slash_o157 [rule_format] : "'\\o157' = '\\111'"

slash_o160 [rule_format] : "'\\o160' = '\\112'"

slash_o161 [rule_format] : "'\\o161' = '\\113'"

slash_o162 [rule_format] : "'\\o162' = '\\114'"

slash_o163 [rule_format] : "'\\o163' = '\\115'"

slash_o164 [rule_format] : "'\\o164' = '\\116'"

slash_o165 [rule_format] : "'\\o165' = '\\117'"

slash_o166 [rule_format] : "'\\o166' = '\\118'"

slash_o167 [rule_format] : "'\\o167' = '\\119'"

slash_o170 [rule_format] : "'\\o170' = '\\120'"

slash_o171 [rule_format] : "'\\o171' = '\\121'"

slash_o172 [rule_format] : "'\\o172' = '\\122'"

slash_o173 [rule_format] : "'\\o173' = '\\123'"

slash_o174 [rule_format] : "'\\o174' = '\\124'"

slash_o175 [rule_format] : "'\\o175' = '\\125'"

slash_o176 [rule_format] : "'\\o176' = '\\126'"

slash_o177 [rule_format] : "'\\o177' = '\\127'"

slash_o200 [rule_format] : "'\\o200' = '\\128'"

slash_o201 [rule_format] : "'\\o201' = '\\129'"

slash_o202 [rule_format] : "'\\o202' = '\\130'"

slash_o203 [rule_format] : "'\\o203' = '\\131'"

slash_o204 [rule_format] : "'\\o204' = '\\132'"

slash_o205 [rule_format] : "'\\o205' = '\\133'"

slash_o206 [rule_format] : "'\\o206' = '\\134'"

slash_o207 [rule_format] : "'\\o207' = '\\135'"

slash_o210 [rule_format] : "'\\o210' = '\\136'"

slash_o211 [rule_format] : "'\\o211' = '\\137'"

slash_o212 [rule_format] : "'\\o212' = '\\138'"

slash_o213 [rule_format] : "'\\o213' = '\\139'"

slash_o214 [rule_format] : "'\\o214' = '\\140'"

slash_o215 [rule_format] : "'\\o215' = '\\141'"

slash_o216 [rule_format] : "'\\o216' = '\\142'"

slash_o217 [rule_format] : "'\\o217' = '\\143'"

slash_o220 [rule_format] : "'\\o220' = '\\144'"

slash_o221 [rule_format] : "'\\o221' = '\\145'"

slash_o222 [rule_format] : "'\\o222' = '\\146'"

slash_o223 [rule_format] : "'\\o223' = '\\147'"

slash_o224 [rule_format] : "'\\o224' = '\\148'"

slash_o225 [rule_format] : "'\\o225' = '\\149'"

slash_o226 [rule_format] : "'\\o226' = '\\150'"

slash_o227 [rule_format] : "'\\o227' = '\\151'"

slash_o230 [rule_format] : "'\\o230' = '\\152'"

slash_o231 [rule_format] : "'\\o231' = '\\153'"

slash_o232 [rule_format] : "'\\o232' = '\\154'"

slash_o233 [rule_format] : "'\\o233' = '\\155'"

slash_o234 [rule_format] : "'\\o234' = '\\156'"

slash_o235 [rule_format] : "'\\o235' = '\\157'"

slash_o236 [rule_format] : "'\\o236' = '\\158'"

slash_o237 [rule_format] : "'\\o237' = '\\159'"

slash_o240 [rule_format] : "'\\o240' = '\\160'"

slash_o241 [rule_format] : "'\\o241' = '\\161'"

slash_o242 [rule_format] : "'\\o242' = '\\162'"

slash_o243 [rule_format] : "'\\o243' = '\\163'"

slash_o244 [rule_format] : "'\\o244' = '\\164'"

slash_o245 [rule_format] : "'\\o245' = '\\165'"

slash_o246 [rule_format] : "'\\o246' = '\\166'"

slash_o247 [rule_format] : "'\\o247' = '\\167'"

slash_o250 [rule_format] : "'\\o250' = '\\168'"

slash_o251 [rule_format] : "'\\o251' = '\\169'"

slash_o252 [rule_format] : "'\\o252' = '\\170'"

slash_o253 [rule_format] : "'\\o253' = '\\171'"

slash_o254 [rule_format] : "'\\o254' = '\\172'"

slash_o255 [rule_format] : "'\\o255' = '\\173'"

slash_o256 [rule_format] : "'\\o256' = '\\174'"

slash_o257 [rule_format] : "'\\o257' = '\\175'"

slash_o260 [rule_format] : "'\\o260' = '\\176'"

slash_o261 [rule_format] : "'\\o261' = '\\177'"

slash_o262 [rule_format] : "'\\o262' = '\\178'"

slash_o263 [rule_format] : "'\\o263' = '\\179'"

slash_o264 [rule_format] : "'\\o264' = '\\180'"

slash_o265 [rule_format] : "'\\o265' = '\\181'"

slash_o266 [rule_format] : "'\\o266' = '\\182'"

slash_o267 [rule_format] : "'\\o267' = '\\183'"

slash_o270 [rule_format] : "'\\o270' = '\\184'"

slash_o271 [rule_format] : "'\\o271' = '\\185'"

slash_o272 [rule_format] : "'\\o272' = '\\186'"

slash_o273 [rule_format] : "'\\o273' = '\\187'"

slash_o274 [rule_format] : "'\\o274' = '\\188'"

slash_o275 [rule_format] : "'\\o275' = '\\189'"

slash_o276 [rule_format] : "'\\o276' = '\\190'"

slash_o277 [rule_format] : "'\\o277' = '\\191'"

slash_o300 [rule_format] : "'\\o300' = '\\192'"

slash_o301 [rule_format] : "'\\o301' = '\\193'"

slash_o302 [rule_format] : "'\\o302' = '\\194'"

slash_o303 [rule_format] : "'\\o303' = '\\195'"

slash_o304 [rule_format] : "'\\o304' = '\\196'"

slash_o305 [rule_format] : "'\\o305' = '\\197'"

slash_o306 [rule_format] : "'\\o306' = '\\198'"

slash_o307 [rule_format] : "'\\o307' = '\\199'"

slash_o310 [rule_format] : "'\\o310' = '\\200'"

slash_o311 [rule_format] : "'\\o311' = '\\201'"

slash_o312 [rule_format] : "'\\o312' = '\\202'"

slash_o313 [rule_format] : "'\\o313' = '\\203'"

slash_o314 [rule_format] : "'\\o314' = '\\204'"

slash_o315 [rule_format] : "'\\o315' = '\\205'"

slash_o316 [rule_format] : "'\\o316' = '\\206'"

slash_o317 [rule_format] : "'\\o317' = '\\207'"

slash_o320 [rule_format] : "'\\o320' = '\\208'"

slash_o321 [rule_format] : "'\\o321' = '\\209'"

slash_o322 [rule_format] : "'\\o322' = '\\210'"

slash_o323 [rule_format] : "'\\o323' = '\\211'"

slash_o324 [rule_format] : "'\\o324' = '\\212'"

slash_o325 [rule_format] : "'\\o325' = '\\213'"

slash_o326 [rule_format] : "'\\o326' = '\\214'"

slash_o327 [rule_format] : "'\\o327' = '\\215'"

slash_o330 [rule_format] : "'\\o330' = '\\216'"

slash_o331 [rule_format] : "'\\o331' = '\\217'"

slash_o332 [rule_format] : "'\\o332' = '\\218'"

slash_o333 [rule_format] : "'\\o333' = '\\219'"

slash_o334 [rule_format] : "'\\o334' = '\\220'"

slash_o335 [rule_format] : "'\\o335' = '\\221'"

slash_o336 [rule_format] : "'\\o336' = '\\222'"

slash_o337 [rule_format] : "'\\o337' = '\\223'"

slash_o340 [rule_format] : "'\\o340' = '\\224'"

slash_o341 [rule_format] : "'\\o341' = '\\225'"

slash_o342 [rule_format] : "'\\o342' = '\\226'"

slash_o343 [rule_format] : "'\\o343' = '\\227'"

slash_o344 [rule_format] : "'\\o344' = '\\228'"

slash_o345 [rule_format] : "'\\o345' = '\\229'"

slash_o346 [rule_format] : "'\\o346' = '\\230'"

slash_o347 [rule_format] : "'\\o347' = '\\231'"

slash_o350 [rule_format] : "'\\o350' = '\\232'"

slash_o351 [rule_format] : "'\\o351' = '\\233'"

slash_o352 [rule_format] : "'\\o352' = '\\234'"

slash_o353 [rule_format] : "'\\o353' = '\\235'"

slash_o354 [rule_format] : "'\\o354' = '\\236'"

slash_o355 [rule_format] : "'\\o355' = '\\237'"

slash_o356 [rule_format] : "'\\o356' = '\\238'"

slash_o357 [rule_format] : "'\\o357' = '\\239'"

slash_o360 [rule_format] : "'\\o360' = '\\240'"

slash_o361 [rule_format] : "'\\o361' = '\\241'"

slash_o362 [rule_format] : "'\\o362' = '\\242'"

slash_o363 [rule_format] : "'\\o363' = '\\243'"

slash_o364 [rule_format] : "'\\o364' = '\\244'"

slash_o365 [rule_format] : "'\\o365' = '\\245'"

slash_o366 [rule_format] : "'\\o366' = '\\246'"

slash_o367 [rule_format] : "'\\o367' = '\\247'"

slash_o370 [rule_format] : "'\\o370' = '\\248'"

slash_o371 [rule_format] : "'\\o371' = '\\249'"

slash_o372 [rule_format] : "'\\o372' = '\\250'"

slash_o373 [rule_format] : "'\\o373' = '\\251'"

slash_o374 [rule_format] : "'\\o374' = '\\252'"

slash_o375 [rule_format] : "'\\o375' = '\\253'"

slash_o376 [rule_format] : "'\\o376' = '\\254'"

slash_o377 [rule_format] : "'\\o377' = '\\255'"

slash_x00 [rule_format] : "'\\x00' = '\\000'"

slash_x01 [rule_format] : "'\\x01' = '\\001'"

slash_x02 [rule_format] : "'\\x02' = '\\002'"

slash_x03 [rule_format] : "'\\x03' = '\\003'"

slash_x04 [rule_format] : "'\\x04' = '\\004'"

slash_x05 [rule_format] : "'\\x05' = '\\005'"

slash_x06 [rule_format] : "'\\x06' = '\\006'"

slash_x07 [rule_format] : "'\\x07' = '\\007'"

slash_x08 [rule_format] : "'\\x08' = '\\008'"

slash_x09 [rule_format] : "'\\x09' = '\\009'"

slash_x0A [rule_format] : "'\\x0A' = '\\010'"

slash_x0B [rule_format] : "'\\x0B' = '\\011'"

slash_x0C [rule_format] : "'\\x0C' = '\\012'"

slash_x0D [rule_format] : "'\\x0D' = '\\013'"

slash_x0E [rule_format] : "'\\x0E' = '\\014'"

slash_x0F [rule_format] : "'\\x0F' = '\\015'"

slash_x10 [rule_format] : "'\\x10' = '\\016'"

slash_x11 [rule_format] : "'\\x11' = '\\017'"

slash_x12 [rule_format] : "'\\x12' = '\\018'"

slash_x13 [rule_format] : "'\\x13' = '\\019'"

slash_x14 [rule_format] : "'\\x14' = '\\020'"

slash_x15 [rule_format] : "'\\x15' = '\\021'"

slash_x16 [rule_format] : "'\\x16' = '\\022'"

slash_x17 [rule_format] : "'\\x17' = '\\023'"

slash_x18 [rule_format] : "'\\x18' = '\\024'"

slash_x19 [rule_format] : "'\\x19' = '\\025'"

slash_x1A [rule_format] : "'\\x1A' = '\\026'"

slash_x1B [rule_format] : "'\\x1B' = '\\027'"

slash_x1C [rule_format] : "'\\x1C' = '\\028'"

slash_x1D [rule_format] : "'\\x1D' = '\\029'"

slash_x1E [rule_format] : "'\\x1E' = '\\030'"

slash_x1F [rule_format] : "'\\x1F' = '\\031'"

slash_x20 [rule_format] : "'\\x20' = '\\032'"

slash_x21 [rule_format] : "'\\x21' = '\\033'"

slash_x22 [rule_format] : "'\\x22' = '\\034'"

slash_x23 [rule_format] : "'\\x23' = '\\035'"

slash_x24 [rule_format] : "'\\x24' = '\\036'"

slash_x25 [rule_format] : "'\\x25' = '\\037'"

slash_x26 [rule_format] : "'\\x26' = '\\038'"

slash_x27 [rule_format] : "'\\x27' = '\\039'"

slash_x28 [rule_format] : "'\\x28' = '\\040'"

slash_x29 [rule_format] : "'\\x29' = '\\041'"

slash_x2A [rule_format] : "'\\x2A' = '\\042'"

slash_x2B [rule_format] : "'\\x2B' = '\\043'"

slash_x2C [rule_format] : "'\\x2C' = '\\044'"

slash_x2D [rule_format] : "'\\x2D' = '\\045'"

slash_x2E [rule_format] : "'\\x2E' = '\\046'"

slash_x2F [rule_format] : "'\\x2F' = '\\047'"

slash_x30 [rule_format] : "'\\x30' = '\\048'"

slash_x31 [rule_format] : "'\\x31' = '\\049'"

slash_x32 [rule_format] : "'\\x32' = '\\050'"

slash_x33 [rule_format] : "'\\x33' = '\\051'"

slash_x34 [rule_format] : "'\\x34' = '\\052'"

slash_x35 [rule_format] : "'\\x35' = '\\053'"

slash_x36 [rule_format] : "'\\x36' = '\\054'"

slash_x37 [rule_format] : "'\\x37' = '\\055'"

slash_x38 [rule_format] : "'\\x38' = '\\056'"

slash_x39 [rule_format] : "'\\x39' = '\\057'"

slash_x3A [rule_format] : "'\\x3A' = '\\058'"

slash_x3B [rule_format] : "'\\x3B' = '\\059'"

slash_x3C [rule_format] : "'\\x3C' = '\\060'"

slash_x3D [rule_format] : "'\\x3D' = '\\061'"

slash_x3E [rule_format] : "'\\x3E' = '\\062'"

slash_x3F [rule_format] : "'\\x3F' = '\\063'"

slash_x40 [rule_format] : "'\\x40' = '\\064'"

slash_x41 [rule_format] : "'\\x41' = '\\065'"

slash_x42 [rule_format] : "'\\x42' = '\\066'"

slash_x43 [rule_format] : "'\\x43' = '\\067'"

slash_x44 [rule_format] : "'\\x44' = '\\068'"

slash_x45 [rule_format] : "'\\x45' = '\\069'"

slash_x46 [rule_format] : "'\\x46' = '\\070'"

slash_x47 [rule_format] : "'\\x47' = '\\071'"

slash_x48 [rule_format] : "'\\x48' = '\\072'"

slash_x49 [rule_format] : "'\\x49' = '\\073'"

slash_x4A [rule_format] : "'\\x4A' = '\\074'"

slash_x4B [rule_format] : "'\\x4B' = '\\075'"

slash_x4C [rule_format] : "'\\x4C' = '\\076'"

slash_x4D [rule_format] : "'\\x4D' = '\\077'"

slash_x4E [rule_format] : "'\\x4E' = '\\078'"

slash_x4F [rule_format] : "'\\x4F' = '\\079'"

slash_x50 [rule_format] : "'\\x50' = '\\080'"

slash_x51 [rule_format] : "'\\x51' = '\\081'"

slash_x52 [rule_format] : "'\\x52' = '\\082'"

slash_x53 [rule_format] : "'\\x53' = '\\083'"

slash_x54 [rule_format] : "'\\x54' = '\\084'"

slash_x55 [rule_format] : "'\\x55' = '\\085'"

slash_x56 [rule_format] : "'\\x56' = '\\086'"

slash_x57 [rule_format] : "'\\x57' = '\\087'"

slash_x58 [rule_format] : "'\\x58' = '\\088'"

slash_x59 [rule_format] : "'\\x59' = '\\089'"

slash_x5A [rule_format] : "'\\x5A' = '\\090'"

slash_x5B [rule_format] : "'\\x5B' = '\\091'"

slash_x5C [rule_format] : "'\\x5C' = '\\092'"

slash_x5D [rule_format] : "'\\x5D' = '\\093'"

slash_x5E [rule_format] : "'\\x5E' = '\\094'"

slash_x5F [rule_format] : "'\\x5F' = '\\095'"

slash_x60 [rule_format] : "'\\x60' = '\\096'"

slash_x61 [rule_format] : "'\\x61' = '\\097'"

slash_x62 [rule_format] : "'\\x62' = '\\098'"

slash_x63 [rule_format] : "'\\x63' = '\\099'"

slash_x64 [rule_format] : "'\\x64' = '\\100'"

slash_x65 [rule_format] : "'\\x65' = '\\101'"

slash_x66 [rule_format] : "'\\x66' = '\\102'"

slash_x67 [rule_format] : "'\\x67' = '\\103'"

slash_x68 [rule_format] : "'\\x68' = '\\104'"

slash_x69 [rule_format] : "'\\x69' = '\\105'"

slash_x6A [rule_format] : "'\\x6A' = '\\106'"

slash_x6B [rule_format] : "'\\x6B' = '\\107'"

slash_x6C [rule_format] : "'\\x6C' = '\\108'"

slash_x6D [rule_format] : "'\\x6D' = '\\109'"

slash_x6E [rule_format] : "'\\x6E' = '\\110'"

slash_x6F [rule_format] : "'\\x6F' = '\\111'"

slash_x70 [rule_format] : "'\\x70' = '\\112'"

slash_x71 [rule_format] : "'\\x71' = '\\113'"

slash_x72 [rule_format] : "'\\x72' = '\\114'"

slash_x73 [rule_format] : "'\\x73' = '\\115'"

slash_x74 [rule_format] : "'\\x74' = '\\116'"

slash_x75 [rule_format] : "'\\x75' = '\\117'"

slash_x76 [rule_format] : "'\\x76' = '\\118'"

slash_x77 [rule_format] : "'\\x77' = '\\119'"

slash_x78 [rule_format] : "'\\x78' = '\\120'"

slash_x79 [rule_format] : "'\\x79' = '\\121'"

slash_x7A [rule_format] : "'\\x7A' = '\\122'"

slash_x7B [rule_format] : "'\\x7B' = '\\123'"

slash_x7C [rule_format] : "'\\x7C' = '\\124'"

slash_x7D [rule_format] : "'\\x7D' = '\\125'"

slash_x7E [rule_format] : "'\\x7E' = '\\126'"

slash_x7F [rule_format] : "'\\x7F' = '\\127'"

slash_x80 [rule_format] : "'\\x80' = '\\128'"

slash_x81 [rule_format] : "'\\x81' = '\\129'"

slash_x82 [rule_format] : "'\\x82' = '\\130'"

slash_x83 [rule_format] : "'\\x83' = '\\131'"

slash_x84 [rule_format] : "'\\x84' = '\\132'"

slash_x85 [rule_format] : "'\\x85' = '\\133'"

slash_x86 [rule_format] : "'\\x86' = '\\134'"

slash_x87 [rule_format] : "'\\x87' = '\\135'"

slash_x88 [rule_format] : "'\\x88' = '\\136'"

slash_x89 [rule_format] : "'\\x89' = '\\137'"

slash_x8A [rule_format] : "'\\x8A' = '\\138'"

slash_x8B [rule_format] : "'\\x8B' = '\\139'"

slash_x8C [rule_format] : "'\\x8C' = '\\140'"

slash_x8D [rule_format] : "'\\x8D' = '\\141'"

slash_x8E [rule_format] : "'\\x8E' = '\\142'"

slash_x8F [rule_format] : "'\\x8F' = '\\143'"

slash_x90 [rule_format] : "'\\x90' = '\\144'"

slash_x91 [rule_format] : "'\\x91' = '\\145'"

slash_x92 [rule_format] : "'\\x92' = '\\146'"

slash_x93 [rule_format] : "'\\x93' = '\\147'"

slash_x94 [rule_format] : "'\\x94' = '\\148'"

slash_x95 [rule_format] : "'\\x95' = '\\149'"

slash_x96 [rule_format] : "'\\x96' = '\\150'"

slash_x97 [rule_format] : "'\\x97' = '\\151'"

slash_x98 [rule_format] : "'\\x98' = '\\152'"

slash_x99 [rule_format] : "'\\x99' = '\\153'"

slash_x9A [rule_format] : "'\\x9A' = '\\154'"

slash_x9B [rule_format] : "'\\x9B' = '\\155'"

slash_x9C [rule_format] : "'\\x9C' = '\\156'"

slash_x9D [rule_format] : "'\\x9D' = '\\157'"

slash_x9E [rule_format] : "'\\x9E' = '\\158'"

slash_x9F [rule_format] : "'\\x9F' = '\\159'"

slash_xA0 [rule_format] : "'\\xA0' = '\\160'"

slash_xA1 [rule_format] : "'\\xA1' = '\\161'"

slash_xA2 [rule_format] : "'\\xA2' = '\\162'"

slash_xA3 [rule_format] : "'\\xA3' = '\\163'"

slash_xA4 [rule_format] : "'\\xA4' = '\\164'"

slash_xA5 [rule_format] : "'\\xA5' = '\\165'"

slash_xA6 [rule_format] : "'\\xA6' = '\\166'"

slash_xA7 [rule_format] : "'\\xA7' = '\\167'"

slash_xA8 [rule_format] : "'\\xA8' = '\\168'"

slash_xA9 [rule_format] : "'\\xA9' = '\\169'"

slash_xAA [rule_format] : "'\\xAA' = '\\170'"

slash_xAB [rule_format] : "'\\xAB' = '\\171'"

slash_xAC [rule_format] : "'\\xAC' = '\\172'"

slash_xAD [rule_format] : "'\\xAD' = '\\173'"

slash_xAE [rule_format] : "'\\xAE' = '\\174'"

slash_xAF [rule_format] : "'\\xAF' = '\\175'"

slash_xB0 [rule_format] : "'\\xB0' = '\\176'"

slash_xB1 [rule_format] : "'\\xB1' = '\\177'"

slash_xB2 [rule_format] : "'\\xB2' = '\\178'"

slash_xB3 [rule_format] : "'\\xB3' = '\\179'"

slash_xB4 [rule_format] : "'\\xB4' = '\\180'"

slash_xB5 [rule_format] : "'\\xB5' = '\\181'"

slash_xB6 [rule_format] : "'\\xB6' = '\\182'"

slash_xB7 [rule_format] : "'\\xB7' = '\\183'"

slash_xB8 [rule_format] : "'\\xB8' = '\\184'"

slash_xB9 [rule_format] : "'\\xB9' = '\\185'"

slash_xBA [rule_format] : "'\\xBA' = '\\186'"

slash_xBB [rule_format] : "'\\xBB' = '\\187'"

slash_xBC [rule_format] : "'\\xBC' = '\\188'"

slash_xBD [rule_format] : "'\\xBD' = '\\189'"

slash_xBE [rule_format] : "'\\xBE' = '\\190'"

slash_xBF [rule_format] : "'\\xBF' = '\\191'"

slash_xC0 [rule_format] : "'\\xC0' = '\\192'"

slash_xC1 [rule_format] : "'\\xC1' = '\\193'"

slash_xC2 [rule_format] : "'\\xC2' = '\\194'"

slash_xC3 [rule_format] : "'\\xC3' = '\\195'"

slash_xC4 [rule_format] : "'\\xC4' = '\\196'"

slash_xC5 [rule_format] : "'\\xC5' = '\\197'"

slash_xC6 [rule_format] : "'\\xC6' = '\\198'"

slash_xC7 [rule_format] : "'\\xC7' = '\\199'"

slash_xC8 [rule_format] : "'\\xC8' = '\\200'"

slash_xC9 [rule_format] : "'\\xC9' = '\\201'"

slash_xCA [rule_format] : "'\\xCA' = '\\202'"

slash_xCB [rule_format] : "'\\xCB' = '\\203'"

slash_xCC [rule_format] : "'\\xCC' = '\\204'"

slash_xCD [rule_format] : "'\\xCD' = '\\205'"

slash_xCE [rule_format] : "'\\xCE' = '\\206'"

slash_xCF [rule_format] : "'\\xCF' = '\\207'"

slash_xD0 [rule_format] : "'\\xD0' = '\\208'"

slash_xD1 [rule_format] : "'\\xD1' = '\\209'"

slash_xD2 [rule_format] : "'\\xD2' = '\\210'"

slash_xD3 [rule_format] : "'\\xD3' = '\\211'"

slash_xD4 [rule_format] : "'\\xD4' = '\\212'"

slash_xD5 [rule_format] : "'\\xD5' = '\\213'"

slash_xD6 [rule_format] : "'\\xD6' = '\\214'"

slash_xD7 [rule_format] : "'\\xD7' = '\\215'"

slash_xD8 [rule_format] : "'\\xD8' = '\\216'"

slash_xD9 [rule_format] : "'\\xD9' = '\\217'"

slash_xDA [rule_format] : "'\\xDA' = '\\218'"

slash_xDB [rule_format] : "'\\xDB' = '\\219'"

slash_xDC [rule_format] : "'\\xDC' = '\\220'"

slash_xDD [rule_format] : "'\\xDD' = '\\221'"

slash_xDE [rule_format] : "'\\xDE' = '\\222'"

slash_xDF [rule_format] : "'\\xDF' = '\\223'"

slash_xE0 [rule_format] : "'\\xE0' = '\\224'"

slash_xE1 [rule_format] : "'\\xE1' = '\\225'"

slash_xE2 [rule_format] : "'\\xE2' = '\\226'"

slash_xE3 [rule_format] : "'\\xE3' = '\\227'"

slash_xE4 [rule_format] : "'\\xE4' = '\\228'"

slash_xE5 [rule_format] : "'\\xE5' = '\\229'"

slash_xE6 [rule_format] : "'\\xE6' = '\\230'"

slash_xE7 [rule_format] : "'\\xE7' = '\\231'"

slash_xE8 [rule_format] : "'\\xE8' = '\\232'"

slash_xE9 [rule_format] : "'\\xE9' = '\\233'"

slash_xEA [rule_format] : "'\\xEA' = '\\234'"

slash_xEB [rule_format] : "'\\xEB' = '\\235'"

slash_xEC [rule_format] : "'\\xEC' = '\\236'"

slash_xED [rule_format] : "'\\xED' = '\\237'"

slash_xEE [rule_format] : "'\\xEE' = '\\238'"

slash_xEF [rule_format] : "'\\xEF' = '\\239'"

slash_xF0 [rule_format] : "'\\xF0' = '\\240'"

slash_xF1 [rule_format] : "'\\xF1' = '\\241'"

slash_xF2 [rule_format] : "'\\xF2' = '\\242'"

slash_xF3 [rule_format] : "'\\xF3' = '\\243'"

slash_xF4 [rule_format] : "'\\xF4' = '\\244'"

slash_xF5 [rule_format] : "'\\xF5' = '\\245'"

slash_xF6 [rule_format] : "'\\xF6' = '\\246'"

slash_xF7 [rule_format] : "'\\xF7' = '\\247'"

slash_xF8 [rule_format] : "'\\xF8' = '\\248'"

slash_xF9 [rule_format] : "'\\xF9' = '\\249'"

slash_xFA [rule_format] : "'\\xFA' = '\\250'"

slash_xFB [rule_format] : "'\\xFB' = '\\251'"

slash_xFC [rule_format] : "'\\xFC' = '\\252'"

slash_xFD [rule_format] : "'\\xFD' = '\\253'"

slash_xFE [rule_format] : "'\\xFE' = '\\254'"

slash_xFF [rule_format] : "'\\xFF' = '\\255'"

NUL_def [rule_format] : "NUL = '\\000'"

SOH_def [rule_format] : "SOH = '\\001'"

SYX_def [rule_format] : "SYX = '\\002'"

ETX_def [rule_format] : "ETX = '\\003'"

EOT_def [rule_format] : "EOT = '\\004'"

ENQ_def [rule_format] : "ENQ = '\\005'"

ACK_def [rule_format] : "ACK = '\\006'"

BEL_def [rule_format] : "BEL = '\\007'"

BS_def [rule_format] : "BS = '\\008'"

HT_def [rule_format] : "HT = '\\009'"

LF_def [rule_format] : "LF = '\\010'"

VT_def [rule_format] : "VT = '\\011'"

FF_def [rule_format] : "FF = '\\012'"

CR_def [rule_format] : "CR = '\\013'"

SO_def [rule_format] : "SO = '\\014'"

SI_def [rule_format] : "SI = '\\015'"

DLE_def [rule_format] : "DLE = '\\016'"

DC1_def [rule_format] : "DC1 = '\\017'"

DC2_def [rule_format] : "DC2 = '\\018'"

DC3_def [rule_format] : "DC3 = '\\019'"

DC4_def [rule_format] : "DC4 = '\\020'"

NAK_def [rule_format] : "NAK = '\\021'"

SYN_def [rule_format] : "SYN = '\\022'"

ETB_def [rule_format] : "ETB = '\\023'"

CAN_def [rule_format] : "CAN = '\\024'"

EM_def [rule_format] : "EM = '\\025'"

SUB_def [rule_format] : "SUB = '\\026'"

ESC_def [rule_format] : "ESC = '\\027'"

FS_def [rule_format] : "FS = '\\028'"

GS_def [rule_format] : "GS = '\\029'"

RS_def [rule_format] : "RS = '\\030'"

US_def [rule_format] : "US = '\\031'"

SP_def [rule_format] : "SP = '\\032'"

DEL_def [rule_format] : "DEL = '\\127'"

NL_def [rule_format] : "NL = LF"

NP_def [rule_format] : "NP = FF"

slash_n [rule_format] : "'\\n' = NL"

slash_t [rule_format] : "'\\t' = HT"

slash_v [rule_format] : "'\\v' = VT"

slash_b [rule_format] : "'\\b' = BS"

slash_r [rule_format] : "'\\r' = CR"

slash_f [rule_format] : "'\\f' = FF"

slash_a [rule_format] : "'\\a' = BEL"

slash_quest [rule_format] : "'\\?' = '?'"

ga_generated_Int [rule_format] :
"ALL (p_Int :: X_Int => bool).
 (ALL (x_1 :: X_Nat). ALL (x_2 :: X_Nat). p_Int (x_1 -'' x_2)) -->
 (ALL (x :: X_Int). p_Int x)"

equality_Int [rule_format] :
"ALL (a :: X_Nat).
 ALL (b :: X_Nat).
 ALL (c :: X_Nat).
 ALL (d :: X_Nat). a -'' b = c -'' d = (a +'' d = c +'' b)"

Nat2Int_embedding [rule_format] :
"ALL (a :: X_Nat). (X_gn_inj :: X_Nat => X_Int) a = a -'' 0''"

ga_comm___XPlus___80 [rule_format] :
"ALL (x :: X_Int). ALL (y :: X_Int). x +' y = y +' x"

ga_assoc___XPlus___86 [rule_format] :
"ALL (x :: X_Int).
 ALL (y :: X_Int). ALL (z :: X_Int). (x +' y) +' z = x +' (y +' z)"

ga_right_unit___XPlus___77 [rule_format] :
"ALL (x :: X_Int). x +' (X_gn_inj :: X_Nat => X_Int) 0'' = x"

ga_left_unit___XPlus___78 [rule_format] :
"ALL (x :: X_Int). (X_gn_inj :: X_Nat => X_Int) 0'' +' x = x"

ga_left_comm___XPlus___85 [rule_format] :
"ALL (x :: X_Int).
 ALL (y :: X_Int). ALL (z :: X_Int). x +' (y +' z) = y +' (x +' z)"

ga_comm___Xx___79 [rule_format] :
"ALL (x :: X_Int). ALL (y :: X_Int). x *' y = y *' x"

ga_assoc___Xx___84 [rule_format] :
"ALL (x :: X_Int).
 ALL (y :: X_Int). ALL (z :: X_Int). (x *' y) *' z = x *' (y *' z)"

ga_right_unit___Xx___75 [rule_format] :
"ALL (x :: X_Int). x *' (X_gn_inj :: Pos => X_Int) 1_3 = x"

ga_left_unit___Xx___76 [rule_format] :
"ALL (x :: X_Int). (X_gn_inj :: Pos => X_Int) 1_3 *' x = x"

ga_left_comm___Xx___83 [rule_format] :
"ALL (x :: X_Int).
 ALL (y :: X_Int). ALL (z :: X_Int). x *' (y *' z) = y *' (x *' z)"

ga_comm_min_82 [rule_format] :
"ALL (x :: X_Int). ALL (y :: X_Int). min'(x, y) = min'(y, x)"

ga_comm_max_81 [rule_format] :
"ALL (x :: X_Int). ALL (y :: X_Int). max'(x, y) = max'(y, x)"

ga_assoc_min_90 [rule_format] :
"ALL (x :: X_Int).
 ALL (y :: X_Int).
 ALL (z :: X_Int). min'(min'(x, y), z) = min'(x, min'(y, z))"

ga_assoc_max_88 [rule_format] :
"ALL (x :: X_Int).
 ALL (y :: X_Int).
 ALL (z :: X_Int). max'(max'(x, y), z) = max'(x, max'(y, z))"

ga_left_comm_min_89 [rule_format] :
"ALL (x :: X_Int).
 ALL (y :: X_Int).
 ALL (z :: X_Int). min'(x, min'(y, z)) = min'(y, min'(x, z))"

ga_left_comm_max_87 [rule_format] :
"ALL (x :: X_Int).
 ALL (y :: X_Int).
 ALL (z :: X_Int). max'(x, max'(y, z)) = max'(y, max'(x, z))"

leq_def_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int).
 (m <=' X_n) =
 defOp ((X_gn_proj :: X_Int => X_Nat partial) (X_n -' m))"

geq_def_Int [rule_format] :
"ALL (m :: X_Int). ALL (X_n :: X_Int). (m >=' X_n) = (X_n <=' m)"

less_def_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int). (m <' X_n) = (m <=' X_n & ~ m = X_n)"

greater_def_Int [rule_format] :
"ALL (m :: X_Int). ALL (X_n :: X_Int). (m >' X_n) = (X_n <' m)"

even_def_Int [rule_format] :
"ALL (m :: X_Int). even'(m) = even''(abs'(m))"

odd_def_Int [rule_format] :
"ALL (m :: X_Int). odd'(m) = (~ even'(m))"

odd_alt_Int [rule_format] :
"ALL (m :: X_Int). odd'(m) = odd''(abs'(m))"

neg_def_Int [rule_format] :
"ALL (a :: X_Nat). ALL (b :: X_Nat). -' (a -'' b) = b -'' a"

sign_def_Int [rule_format] :
"ALL (m :: X_Int).
 sign(m) =
 (if m = (X_gn_inj :: X_Nat => X_Int) 0''
     then (X_gn_inj :: X_Nat => X_Int) 0''
     else if m >' (X_gn_inj :: X_Nat => X_Int) 0''
             then (X_gn_inj :: Pos => X_Int) 1_3
             else -' (X_gn_inj :: Pos => X_Int) 1_3)"

abs_def_Int [rule_format] :
"ALL (m :: X_Int).
 (X_gn_inj :: X_Nat => X_Int) (abs'(m)) =
 (if m <' (X_gn_inj :: X_Nat => X_Int) 0'' then -' m else m)"

add_def_Int [rule_format] :
"ALL (a :: X_Nat).
 ALL (b :: X_Nat).
 ALL (c :: X_Nat).
 ALL (d :: X_Nat). (a -'' b) +' (c -'' d) = (a +'' c) -'' (b +'' d)"

mult_def_Int [rule_format] :
"ALL (a :: X_Nat).
 ALL (b :: X_Nat).
 ALL (c :: X_Nat).
 ALL (d :: X_Nat).
 (a -'' b) *' (c -'' d) =
 ((a *'' c) +'' (b *'' d)) -'' ((b *'' c) +'' (a *'' d))"

sub_def_Int [rule_format] :
"ALL (m :: X_Int). ALL (X_n :: X_Int). m -' X_n = m +' -' X_n"

min_def_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int). min'(m, X_n) = (if m <=' X_n then m else X_n)"

max_def_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int). max'(m, X_n) = (if m <=' X_n then X_n else m)"

power_neg1_Int [rule_format] :
"ALL (a :: X_Nat).
 -' (X_gn_inj :: Pos => X_Int) 1_3 ^' a =
 (if even''(a) then (X_gn_inj :: Pos => X_Int) 1_3
     else -' (X_gn_inj :: Pos => X_Int) 1_3)"

power_others_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (a :: X_Nat).
 ~ m = -' (X_gn_inj :: Pos => X_Int) 1_3 -->
 m ^' a =
 (sign(m) ^' a) *' (X_gn_inj :: X_Nat => X_Int) (abs'(m) ^'' a)"

divide_dom2_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int).
 defOp (m /?' X_n) = (m mod' X_n = makePartial 0'')"

divide_alt_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int).
 ALL (r :: X_Int).
 m /?' X_n = makePartial r =
 (~ X_n = (X_gn_inj :: X_Nat => X_Int) 0'' & X_n *' r = m)"

divide_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int).
 m /?' X_n =
 restrictOp
 (makePartial
  ((sign(m) *' sign(X_n)) *'
   (X_gn_inj :: X_Nat => X_Int) (makeTotal (abs'(m) /?'' abs'(X_n)))))
 (defOp (abs'(m) /?'' abs'(X_n)))"

div_dom_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int).
 defOp (m div' X_n) = (~ X_n = (X_gn_inj :: X_Nat => X_Int) 0'')"

div_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int).
 ALL (r :: X_Int).
 m div' X_n = makePartial r =
 (EX (a :: X_Nat).
  m = (X_n *' r) +' (X_gn_inj :: X_Nat => X_Int) a &
  a <'' abs'(X_n))"

quot_dom_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int).
 defOp (m quot' X_n) = (~ X_n = (X_gn_inj :: X_Nat => X_Int) 0'')"

quot_neg_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int).
 ALL (r :: X_Int).
 m <' (X_gn_inj :: X_Nat => X_Int) 0'' -->
 m quot' X_n = makePartial r =
 (EX (s :: X_Int).
  m = (X_n *' r) +' s &
  (X_gn_inj :: X_Nat => X_Int) 0'' >=' s &
  s >' -' (X_gn_inj :: X_Nat => X_Int) (abs'(X_n)))"

quot_nonneg_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int).
 ALL (r :: X_Int).
 m >=' (X_gn_inj :: X_Nat => X_Int) 0'' -->
 m quot' X_n = makePartial r =
 (EX (s :: X_Int).
  m = (X_n *' r) +' s &
  (X_gn_inj :: X_Nat => X_Int) 0'' <=' s &
  s <' (X_gn_inj :: X_Nat => X_Int) (abs'(X_n)))"

rem_dom_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int).
 defOp (m rem' X_n) = (~ X_n = (X_gn_inj :: X_Nat => X_Int) 0'')"

quot_rem_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int).
 ALL (s :: X_Int).
 m <' (X_gn_inj :: X_Nat => X_Int) 0'' -->
 m rem' X_n = makePartial s =
 (EX (r :: X_Int).
  m = (X_n *' r) +' s &
  (X_gn_inj :: X_Nat => X_Int) 0'' >=' s &
  s >' -' (X_gn_inj :: X_Nat => X_Int) (abs'(X_n)))"

rem_nonneg_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int).
 ALL (s :: X_Int).
 m >=' (X_gn_inj :: X_Nat => X_Int) 0'' -->
 m rem' X_n = makePartial s =
 (EX (r :: X_Int).
  m = (X_n *' r) +' s &
  (X_gn_inj :: X_Nat => X_Int) 0'' <=' s &
  s <' (X_gn_inj :: X_Nat => X_Int) (abs'(X_n)))"

mod_dom_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int).
 defOp (m mod' X_n) = (~ X_n = (X_gn_inj :: X_Nat => X_Int) 0'')"

mod_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int).
 ALL (a :: X_Nat).
 m mod' X_n = makePartial a =
 (EX (r :: X_Int).
  m = (X_n *' r) +' (X_gn_inj :: X_Nat => X_Int) a &
  a <'' abs'(X_n))"

distr1_Int [rule_format] :
"ALL (r :: X_Int).
 ALL (s :: X_Int).
 ALL (t :: X_Int). (r +' s) *' t = (r *' t) +' (s *' t)"

distr2_Int [rule_format] :
"ALL (r :: X_Int).
 ALL (s :: X_Int).
 ALL (t :: X_Int). t *' (r +' s) = (t *' r) +' (t *' s)"

Int_Nat_sub_compat [rule_format] :
"ALL (a :: X_Nat).
 ALL (b :: X_Nat).
 defOp (a -? b) -->
 restrictOp
 (makePartial ((X_gn_inj :: X_Nat => X_Int) (makeTotal (a -? b))))
 (defOp (a -? b)) =
 makePartial (a -'' b)"

abs_decomp_Int [rule_format] :
"ALL (m :: X_Int).
 m = sign(m) *' (X_gn_inj :: X_Nat => X_Int) (abs'(m))"

mod_abs_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int).
 m mod' X_n = m mod' (X_gn_inj :: X_Nat => X_Int) (abs'(X_n))"

div_mod_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int).
 ~ X_n = (X_gn_inj :: X_Nat => X_Int) 0'' -->
 makePartial m =
 restrictOp
 (makePartial
  ((makeTotal (m div' X_n) *' X_n) +'
   (X_gn_inj :: X_Nat => X_Int) (makeTotal (m mod' X_n))))
 (defOp (m div' X_n) & defOp (m mod' X_n))"

quot_abs_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int).
 restrictOp
 (makePartial
  ((X_gn_inj :: X_Nat => X_Int) (abs'(makeTotal (m quot' X_n)))))
 (defOp (m quot' X_n)) =
 (X_gn_inj :: X_Nat => X_Int) (abs'(m)) quot'
 (X_gn_inj :: X_Nat => X_Int) (abs'(X_n))"

rem_abs_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int).
 restrictOp
 (makePartial
  ((X_gn_inj :: X_Nat => X_Int) (abs'(makeTotal (m rem' X_n)))))
 (defOp (m rem' X_n)) =
 (X_gn_inj :: X_Nat => X_Int) (abs'(m)) rem'
 (X_gn_inj :: X_Nat => X_Int) (abs'(X_n))"

quot_rem_Int_123 [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int).
 ~ X_n = (X_gn_inj :: X_Nat => X_Int) 0'' -->
 makePartial m =
 restrictOp
 (makePartial
  ((makeTotal (m quot' X_n) *' X_n) +' makeTotal (m rem' X_n)))
 (defOp (m quot' X_n) & defOp (m rem' X_n))"

power_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (a :: X_Nat).
 ALL (b :: X_Nat). m ^' (a +'' b) = (m ^' a) *' (m ^' b)"

ga_generated_Rat [rule_format] :
"ALL (p_Rat :: Rat => bool).
 (ALL (x_1 :: X_Int). ALL (x_2 :: Pos). p_Rat (x_1 /' x_2)) -->
 (ALL (x :: Rat). p_Rat x)"

equality_Rat [rule_format] :
"ALL (i :: X_Int).
 ALL (j :: X_Int).
 ALL (p :: Pos).
 ALL (q :: Pos).
 i /' p = j /' q =
 (i *' (X_gn_inj :: Pos => X_Int) q =
  j *' (X_gn_inj :: Pos => X_Int) p)"

Int2Rat_embedding [rule_format] :
"ALL (i :: X_Int). (X_gn_inj :: X_Int => Rat) i = i /' 1_3"

ga_comm___XPlus___139 [rule_format] :
"ALL (x :: Rat). ALL (y :: Rat). x +_5 y = y +_5 x"

ga_assoc___XPlus___145 [rule_format] :
"ALL (x :: Rat).
 ALL (y :: Rat). ALL (z :: Rat). (x +_5 y) +_5 z = x +_5 (y +_5 z)"

ga_right_unit___XPlus___136 [rule_format] :
"ALL (x :: Rat). x +_5 (X_gn_inj :: X_Nat => Rat) 0'' = x"

ga_left_unit___XPlus___137 [rule_format] :
"ALL (x :: Rat). (X_gn_inj :: X_Nat => Rat) 0'' +_5 x = x"

ga_left_comm___XPlus___144 [rule_format] :
"ALL (x :: Rat).
 ALL (y :: Rat). ALL (z :: Rat). x +_5 (y +_5 z) = y +_5 (x +_5 z)"

ga_comm___Xx___138 [rule_format] :
"ALL (x :: Rat). ALL (y :: Rat). x *_4 y = y *_4 x"

ga_assoc___Xx___143 [rule_format] :
"ALL (x :: Rat).
 ALL (y :: Rat). ALL (z :: Rat). (x *_4 y) *_4 z = x *_4 (y *_4 z)"

ga_right_unit___Xx___134 [rule_format] :
"ALL (x :: Rat). x *_4 (X_gn_inj :: Pos => Rat) 1_3 = x"

ga_left_unit___Xx___135 [rule_format] :
"ALL (x :: Rat). (X_gn_inj :: Pos => Rat) 1_3 *_4 x = x"

ga_left_comm___Xx___142 [rule_format] :
"ALL (x :: Rat).
 ALL (y :: Rat). ALL (z :: Rat). x *_4 (y *_4 z) = y *_4 (x *_4 z)"

ga_comm_min_141 [rule_format] :
"ALL (x :: Rat). ALL (y :: Rat). min_3(x, y) = min_3(y, x)"

ga_comm_max_140 [rule_format] :
"ALL (x :: Rat). ALL (y :: Rat). max_3(x, y) = max_3(y, x)"

ga_assoc_min_149 [rule_format] :
"ALL (x :: Rat).
 ALL (y :: Rat).
 ALL (z :: Rat). min_3(min_3(x, y), z) = min_3(x, min_3(y, z))"

ga_assoc_max_147 [rule_format] :
"ALL (x :: Rat).
 ALL (y :: Rat).
 ALL (z :: Rat). max_3(max_3(x, y), z) = max_3(x, max_3(y, z))"

ga_left_comm_min_148 [rule_format] :
"ALL (x :: Rat).
 ALL (y :: Rat).
 ALL (z :: Rat). min_3(x, min_3(y, z)) = min_3(y, min_3(x, z))"

ga_left_comm_max_146 [rule_format] :
"ALL (x :: Rat).
 ALL (y :: Rat).
 ALL (z :: Rat). max_3(x, max_3(y, z)) = max_3(y, max_3(x, z))"

leq_def_Rat [rule_format] :
"ALL (p :: Pos).
 ALL (q :: Pos).
 ALL (i :: X_Int).
 ALL (j :: X_Int).
 (i /' p <=_3 j /' q) =
 (i *' (X_gn_inj :: Pos => X_Int) q <='
  j *' (X_gn_inj :: Pos => X_Int) p)"

geq_def_Rat [rule_format] :
"ALL (x :: Rat). ALL (y :: Rat). (x >=_3 y) = (y <=_3 x)"

less_def_Rat [rule_format] :
"ALL (x :: Rat). ALL (y :: Rat). (x <_3 y) = (x <=_3 y & ~ x = y)"

greater_def_Rat [rule_format] :
"ALL (x :: Rat). ALL (y :: Rat). (x >_3 y) = (y <_3 x)"

minus_def_Rat [rule_format] :
"ALL (p :: Pos). ALL (i :: X_Int). -'' (i /' p) = -' i /' p"

abs_def_Rat [rule_format] :
"ALL (p :: Pos).
 ALL (i :: X_Int).
 abs''(i /' p) = (X_gn_inj :: X_Nat => X_Int) (abs'(i)) /' p"

add_def_Rat [rule_format] :
"ALL (p :: Pos).
 ALL (q :: Pos).
 ALL (i :: X_Int).
 ALL (j :: X_Int).
 (i /' p) +_5 (j /' q) =
 ((i *' (X_gn_inj :: Pos => X_Int) q) +'
  (j *' (X_gn_inj :: Pos => X_Int) p))
 /' (p *_3 q)"

sub_def_Rat [rule_format] :
"ALL (x :: Rat). ALL (y :: Rat). x -_3 y = x +_5 -'' y"

mult_def_Rat [rule_format] :
"ALL (p :: Pos).
 ALL (q :: Pos).
 ALL (i :: X_Int).
 ALL (j :: X_Int). (i /' p) *_4 (j /' q) = (i *' j) /' (p *_3 q)"

min_def_Rat [rule_format] :
"ALL (x :: Rat).
 ALL (y :: Rat). min_3(x, y) = (if x <=_3 y then x else y)"

max_def_Rat [rule_format] :
"ALL (x :: Rat).
 ALL (y :: Rat). max_3(x, y) = (if x <=_3 y then y else x)"

divide_def1_Rat [rule_format] :
"ALL (x :: Rat). ~ defOp (x /'' (X_gn_inj :: X_Nat => Rat) 0'')"

divide_def2_Rat [rule_format] :
"ALL (x :: Rat).
 ALL (y :: Rat).
 ALL (z :: Rat).
 ~ y = (X_gn_inj :: X_Nat => Rat) 0'' -->
 x /'' y = makePartial z = (x = z *_4 y)"

power_0_Rat [rule_format] :
"ALL (x :: Rat).
 x ^_3 (X_gn_inj :: X_Nat => X_Int) 0'' =
 makePartial ((X_gn_inj :: Pos => Rat) 1_3)"

power_suc_Rat [rule_format] :
"ALL (X_n :: X_Nat).
 ALL (x :: Rat).
 x ^_3 (X_gn_inj :: Pos => X_Int) (suc''(X_n)) =
 restrictOp
 (makePartial
  (x *_4 makeTotal (x ^_3 (X_gn_inj :: X_Nat => X_Int) X_n)))
 (defOp (x ^_3 (X_gn_inj :: X_Nat => X_Int) X_n))"

power_neg_Rat [rule_format] :
"ALL (p :: Pos).
 ALL (x :: Rat).
 x ^_3 -' (X_gn_inj :: Pos => X_Int) p =
 restrictOp
 ((X_gn_inj :: Pos => Rat) 1_3 /''
  makeTotal (x ^_3 (X_gn_inj :: Pos => X_Int) p))
 (defOp (x ^_3 (X_gn_inj :: Pos => X_Int) p))"

distr1_Rat [rule_format] :
"ALL (x :: Rat).
 ALL (y :: Rat).
 ALL (z :: Rat). (x +_5 y) *_4 z = (x *_4 z) +_5 (y *_4 z)"

distr2_Rat [rule_format] :
"ALL (x :: Rat).
 ALL (y :: Rat).
 ALL (z :: Rat). z *_4 (x +_5 y) = (z *_4 x) +_5 (z *_4 y)"

sub_rule_Rat [rule_format] :
"ALL (i :: X_Int).
 ALL (j :: X_Int).
 ALL (p :: Pos).
 ALL (q :: Pos).
 (i /' p) -_3 (j /' q) =
 ((i *' (X_gn_inj :: Pos => X_Int) q) -'
  (j *' (X_gn_inj :: Pos => X_Int) p))
 /' (p *_3 q)"

divide_dom_Rat [rule_format] :
"ALL (x :: Rat).
 ALL (y :: Rat).
 defOp (x /'' y) = (~ y = (X_gn_inj :: X_Nat => Rat) 0'')"

divide_rule_Rat [rule_format] :
"ALL (i :: X_Int).
 ALL (j :: X_Int).
 ALL (p :: Pos).
 ALL (q :: Pos).
 ~ j = (X_gn_inj :: X_Nat => X_Int) 0'' -->
 (i /' p) /'' (j /' q) =
 (X_gn_inj :: X_Int => Rat) (i *' (X_gn_inj :: Pos => X_Int) q) /''
 (X_gn_inj :: X_Int => Rat) ((X_gn_inj :: Pos => X_Int) p *' j)"

power_Rat [rule_format] :
"ALL (i :: X_Int).
 ALL (j :: X_Int).
 ALL (x :: Rat).
 x ^_3 (i +' j) =
 restrictOp
 (makePartial (makeTotal (x ^_3 i) *_4 makeTotal (x ^_3 j)))
 (defOp (x ^_3 i) & defOp (x ^_3 j))"

AbsSignumLaw [rule_format] :
"ALL (x :: 'a partial). abs_3(x) *_5 signum(x) = x"

IPN01 [rule_format] :
"ALL (x :: Pos).
 ALL (y :: Pos).
 (X_gn_inj :: Pos => X_Int) x +' (X_gn_inj :: Pos => X_Int) y =
 (X_gn_inj :: X_Nat => X_Int)
 ((X_gn_inj :: Pos => X_Nat) x +'' (X_gn_inj :: Pos => X_Nat) y)"

IPN02 [rule_format] :
"ALL (x :: Pos).
 ALL (y :: Pos).
 (X_gn_inj :: Pos => X_Int) x *' (X_gn_inj :: Pos => X_Int) y =
 (X_gn_inj :: X_Nat => X_Int)
 ((X_gn_inj :: Pos => X_Nat) x *'' (X_gn_inj :: Pos => X_Nat) y)"

IPN03 [rule_format] :
"ALL (x :: Pos).
 ALL (y :: Pos).
 (X_gn_inj :: Pos => X_Int) x -' (X_gn_inj :: Pos => X_Int) y =
 (X_gn_inj :: X_Nat => X_Int)
 ((X_gn_inj :: Pos => X_Nat) x -! (X_gn_inj :: Pos => X_Nat) y)"

IPN04 [rule_format] :
"ALL (x :: Pos).
 (X_gn_inj :: Pos partial => X_Nat) (negate(makePartial x)) =
 0'' -! (X_gn_inj :: Pos => X_Nat) x"

IPN05 [rule_format] :
"ALL (x :: Pos). abs_3(makePartial x) = makePartial x"

IPN06 [rule_format] :
"ALL (x :: Pos). signum(makePartial x) = makePartial 1_3"

IPN07 [rule_format] :
"ALL (z :: X_Int).
 fromInteger(z) = (X_gn_proj :: X_Int => Pos partial) z"

INN01 [rule_format] :
"ALL (x :: X_Nat).
 ALL (y :: X_Nat).
 (X_gn_inj :: X_Nat => X_Int) x +' (X_gn_inj :: X_Nat => X_Int) y =
 (X_gn_inj :: X_Nat => X_Int) (x +'' y)"

INN02 [rule_format] :
"ALL (x :: X_Nat).
 ALL (y :: X_Nat).
 (X_gn_inj :: X_Nat => X_Int) x *' (X_gn_inj :: X_Nat => X_Int) y =
 (X_gn_inj :: X_Nat => X_Int) (x *'' y)"

INN03 [rule_format] :
"ALL (x :: X_Nat).
 ALL (y :: X_Nat).
 (X_gn_inj :: X_Nat => X_Int) x -' (X_gn_inj :: X_Nat => X_Int) y =
 (X_gn_inj :: X_Nat => X_Int) (x -! y)"

INN04 [rule_format] :
"ALL (x :: X_Nat). negate(makePartial x) = makePartial (0'' -! x)"

INN05 [rule_format] :
"ALL (x :: X_Nat). abs_3(makePartial x) = makePartial x"

INN06 [rule_format] :
"ALL (x :: X_Nat).
 signum(makePartial x) =
 makePartial ((X_gn_inj :: Pos => X_Nat) 1_3)"

INN07 [rule_format] :
"ALL (z :: X_Int).
 fromInteger(z) = (X_gn_proj :: X_Int => X_Nat partial) z"

IIN01 [rule_format] :
"ALL (x :: X_Int). ALL (y :: X_Int). x +' y = x +' y"

IIN02 [rule_format] :
"ALL (x :: X_Int). ALL (y :: X_Int). x *' y = x *' y"

IIN03 [rule_format] :
"ALL (x :: X_Int). ALL (y :: X_Int). x -' y = x -' y"

IIN04 [rule_format] :
"ALL (x :: X_Int).
 negate(makePartial x) =
 makePartial ((X_gn_inj :: X_Nat => X_Int) 0'' -' x)"

IIN05 [rule_format] :
"ALL (x :: X_Int).
 (X_gn_inj :: X_Int => Rat) x >=_3
 (X_gn_inj :: X_Nat => Rat) 0'' -->
 abs_3(makePartial x) = makePartial x"

IIN06 [rule_format] :
"ALL (x :: X_Int).
 (X_gn_inj :: X_Int => Rat) x <_3 (X_gn_inj :: X_Nat => Rat) 0'' -->
 abs_3(makePartial x) = negate(makePartial x)"

IIN07 [rule_format] :
"ALL (x :: X_Int).
 (X_gn_inj :: X_Int => Rat) x >_3 (X_gn_inj :: X_Nat => Rat) 0'' -->
 signum(makePartial x) =
 makePartial ((X_gn_inj :: Pos => X_Int) 1_3)"

IIN07_1 [rule_format] :
"ALL (x :: X_Int).
 makePartial x =='
 makePartial ((X_gn_inj :: X_Nat => X_Int) 0'') -->
 signum(makePartial x) =
 makePartial ((X_gn_inj :: X_Nat => X_Int) 0'')"

IIN08 [rule_format] :
"ALL (x :: X_Int).
 (X_gn_inj :: X_Int => Rat) x <_3 (X_gn_inj :: X_Nat => Rat) 0'' -->
 signum(makePartial x) =
 makePartial (-' (X_gn_inj :: Pos => X_Int) 1_3)"

IIN09 [rule_format] :
"ALL (x :: X_Int). fromInteger(x) = makePartial x"

IRN01 [rule_format] :
"ALL (x :: Rat). ALL (y :: Rat). x +_5 y = x +_5 y"

IRN02 [rule_format] :
"ALL (x :: Rat). ALL (y :: Rat). x *_4 y = x *_4 y"

IRN03 [rule_format] :
"ALL (x :: Rat). ALL (y :: Rat). x -_3 y = x -_3 y"

IRN04 [rule_format] :
"ALL (x :: Rat).
 negate(makePartial x) =
 makePartial ((X_gn_inj :: X_Nat => Rat) 0'' -_3 x)"

IRN05 [rule_format] :
"ALL (x :: Rat).
 x >=_3 (X_gn_inj :: X_Nat => Rat) 0'' -->
 abs_3(makePartial x) = makePartial x"

IRN06 [rule_format] :
"ALL (x :: Rat).
 x <_3 (X_gn_inj :: X_Nat => Rat) 0'' -->
 abs_3(makePartial x) = negate(makePartial x)"

IRN07 [rule_format] :
"ALL (x :: Rat).
 x >_3 (X_gn_inj :: X_Nat => Rat) 0'' -->
 signum(makePartial x) = makePartial ((X_gn_inj :: Pos => Rat) 1_3)"

IRN07_2 [rule_format] :
"ALL (x :: Rat).
 makePartial x ==' makePartial ((X_gn_inj :: X_Nat => Rat) 0'') -->
 signum(makePartial x) =
 makePartial ((X_gn_inj :: X_Nat => Rat) 0'')"

IRN08 [rule_format] :
"ALL (x :: Rat).
 x <_3 (X_gn_inj :: X_Nat => Rat) 0'' -->
 signum(makePartial x) =
 makePartial
 ((X_gn_inj :: X_Int => Rat) (-' (X_gn_inj :: Pos => X_Int) 1_3))"

IRN09 [rule_format] :
"ALL (z :: X_Int). fromInteger(z) = makePartial (z /' 1_3)"

IRI01 [rule_format] :
"ALL (w :: 'a partial).
 ALL (x :: 'a partial).
 ALL (y :: 'a partial).
 ALL (z :: 'a partial).
 (z, w) = mapSnd id (mapFst id (quotRem x y)) --> x quot'' y = z"

IRI02 [rule_format] :
"ALL (w :: 'a partial).
 ALL (x :: 'a partial).
 ALL (y :: 'a partial).
 ALL (z :: 'a partial).
 (z, w) = mapSnd id (mapFst id (quotRem x y)) --> x rem'' y = w"

IRI03 [rule_format] :
"ALL (w :: 'a partial).
 ALL (x :: 'a partial).
 ALL (y :: 'a partial).
 ALL (z :: 'a partial).
 (z, w) = mapSnd id (mapFst id (divMod x y)) --> x div_3 y = z"

IRI04 [rule_format] :
"ALL (w :: 'a partial).
 ALL (x :: 'a partial).
 ALL (y :: 'a partial).
 ALL (z :: 'a partial).
 (z, w) = mapSnd id (mapFst id (divMod x y)) --> x mod_3 y = w"

IRI05 [rule_format] :
"ALL (s :: 'a partial).
 ALL (w :: 'a partial).
 ALL (x :: 'a partial).
 ALL (y :: 'a partial).
 ALL (z :: 'a partial).
 signum(w) = negate(signum(y)) &
 (z, w) = mapSnd id (mapFst id (quotRem x y)) -->
 mapSnd id (mapFst id (divMod x y)) =
 (z -_4
  fromInteger(toInteger(makePartial
                        ((X_gn_inj :: Pos => X_Nat) 1_3))),
  w +_6 s)"

IRI06 [rule_format] :
"ALL (w :: 'a partial).
 ALL (x :: 'a partial).
 ALL (y :: 'a partial).
 ALL (z :: 'a partial).
 ~ signum(w) = negate(signum(y)) &
 (z, w) = mapSnd id (mapFst id (quotRem x y)) -->
 mapSnd id (mapFst id (divMod x y)) = (z, w)"

IRI01_3 [rule_format] :
"ALL (x :: X_Int).
 makePartial
 ((X_gn_inj :: X_Int partial => Rat) (recip(makePartial x))) =
 (X_gn_inj :: Pos => Rat) 1_3 /'' (X_gn_inj :: X_Int => Rat) x"

IRI02_4 [rule_format] :
"ALL (x :: X_Int).
 ALL (y :: X_Int).
 (X_gn_inj :: X_Int => Rat) x /'' (X_gn_inj :: X_Int => Rat) y =
 restrictOp
 (makePartial
  ((X_gn_inj :: X_Int => Rat)
   (x *' makeTotal (recip(makePartial y)))))
 (defOp (recip(makePartial y)))"

IRF01 [rule_format] :
"ALL (x :: Rat).
 recip(makePartial x) = (X_gn_inj :: Pos => Rat) 1_3 /'' x"

IRF02 [rule_format] :
"ALL (x :: Rat).
 ALL (y :: Rat).
 x /'' y =
 restrictOp (makePartial (x *_4 makeTotal (recip(makePartial y))))
 (defOp (recip(makePartial y)))"

ICE01 [rule_format] :
"ALL (x :: Char partial).
 ALL (y :: Char partial).
 restrictOp (makePartial (ord'(makeTotal x))) (defOp x) =='
 restrictOp (makePartial (ord'(makeTotal y))) (defOp y) =
 x ==' y"

ICE02 [rule_format] :
"ALL (x :: Char partial).
 ALL (y :: Char partial).
 Not'
 (restrictOp (makePartial (ord'(makeTotal x))) (defOp x) =='
  restrictOp (makePartial (ord'(makeTotal y))) (defOp y)) =
 x /= y"

ICO04 [rule_format] :
"ALL (x :: Char partial).
 ALL (y :: Char partial).
 ((defOp x & defOp y) &
  (X_gn_inj :: X_Nat => Rat) (ord'(makeTotal x)) <_3
  (X_gn_inj :: X_Nat => Rat) (ord'(makeTotal y))) =
 x <_4 y"

ICO05 [rule_format] :
"ALL (x :: Char partial).
 ALL (y :: Char partial).
 ((defOp x & defOp y) &
  (X_gn_inj :: X_Nat => Rat) (ord'(makeTotal x)) <=_3
  (X_gn_inj :: X_Nat => Rat) (ord'(makeTotal y))) =
 x <=_4 y"

ICO06 [rule_format] :
"ALL (x :: Char partial).
 ALL (y :: Char partial).
 ((defOp x & defOp y) &
  (X_gn_inj :: X_Nat => Rat) (ord'(makeTotal x)) >_3
  (X_gn_inj :: X_Nat => Rat) (ord'(makeTotal y))) =
 x >_4 y"

ICO07 [rule_format] :
"ALL (x :: Char partial).
 ALL (y :: Char partial).
 ((defOp x & defOp y) &
  (X_gn_inj :: X_Nat => Rat) (ord'(makeTotal x)) >=_3
  (X_gn_inj :: X_Nat => Rat) (ord'(makeTotal y))) =
 x >=_4 y"

ICO01 [rule_format] :
"ALL (x :: Char partial).
 ALL (y :: Char partial).
 compare x y ==' makePartial EQ =
 restrictOp (makePartial (ord'(makeTotal x))) (defOp x) =='
 restrictOp (makePartial (ord'(makeTotal y))) (defOp y)"

ICO02 [rule_format] :
"ALL (x :: Char partial).
 ALL (y :: Char partial).
 compare x y ==' makePartial LT =
 ((defOp x & defOp y) &
  (X_gn_inj :: X_Nat => Rat) (ord'(makeTotal x)) <_3
  (X_gn_inj :: X_Nat => Rat) (ord'(makeTotal y)))"

ICO03 [rule_format] :
"ALL (x :: Char partial).
 ALL (y :: Char partial).
 compare x y ==' makePartial GT =
 ((defOp x & defOp y) &
  (X_gn_inj :: X_Nat => Rat) (ord'(makeTotal x)) >_3
  (X_gn_inj :: X_Nat => Rat) (ord'(makeTotal y)))"

ICO08 [rule_format] :
"ALL (x :: Char partial).
 ALL (y :: Char partial).
 ((defOp x & defOp y) &
  (X_gn_inj :: X_Nat => Rat) (ord'(makeTotal x)) <=_3
  (X_gn_inj :: X_Nat => Rat) (ord'(makeTotal y))) =
 X_maxX4 x y ==' y"

ICO09 [rule_format] :
"ALL (x :: Char partial).
 ALL (y :: Char partial).
 ((defOp y & defOp x) &
  (X_gn_inj :: X_Nat => Rat) (ord'(makeTotal y)) <=_3
  (X_gn_inj :: X_Nat => Rat) (ord'(makeTotal x))) =
 X_maxX4 x y ==' x"

ICO10 [rule_format] :
"ALL (x :: Char partial).
 ALL (y :: Char partial).
 ((defOp x & defOp y) &
  (X_gn_inj :: X_Nat => Rat) (ord'(makeTotal x)) <=_3
  (X_gn_inj :: X_Nat => Rat) (ord'(makeTotal y))) =
 X_minX4 x y ==' x"

ICO11 [rule_format] :
"ALL (x :: Char partial).
 ALL (y :: Char partial).
 ((defOp y & defOp x) &
  (X_gn_inj :: X_Nat => Rat) (ord'(makeTotal y)) <=_3
  (X_gn_inj :: X_Nat => Rat) (ord'(makeTotal x))) =
 X_minX4 x y ==' y"

declare ga_subt_reflexive [simp]
declare ga_subt_Int_XLt_Rat [simp]
declare ga_subt_Nat_XLt_Int [simp]
declare ga_subt_Pos_XLt_Nat [simp]
declare Comp1 [simp]
declare IdDef [simp]
declare FlipDef [simp]
declare FstDef [simp]
declare SndDef [simp]
declare CurryDef [simp]
declare UncurryDef [simp]
declare NotFalse [simp]
declare NotTrue [simp]
declare AndFalse [simp]
declare AndTrue [simp]
declare OtherwiseDef [simp]
declare NotTrue1 [simp]
declare EqualReflex [simp]
declare IUE1 [simp]
declare IUE2 [simp]
declare IBE1 [simp]
declare IBE2 [simp]
declare IBE3 [simp]
declare IBE4 [simp]
declare IBE5 [simp]
declare IBE6 [simp]
declare IBE7 [simp]
declare IBE8 [simp]
declare IOE01 [simp]
declare IOE02 [simp]
declare IOE03 [simp]
declare IOE04 [simp]
declare IOE05 [simp]
declare IOE06 [simp]
declare IOE07 [simp]
declare IOE08 [simp]
declare IOE09 [simp]
declare LeIrreflexivity [simp]
declare LeTAsymmetry [simp]
declare GeIrreflexivity [simp]
declare GeTAsymmetry [simp]
declare GeTTransitive [simp]
declare GeTTotal [simp]
declare LeqReflexivity [simp]
declare LeqTTransitive [simp]
declare LeqTTotal [simp]
declare GeqReflexivity [simp]
declare GeqTTransitive [simp]
declare GeqTTotal [simp]
declare CmpLTDef [simp]
declare CmpEQDef [simp]
declare CmpGTDef [simp]
declare MaxYDef [simp]
declare MaxXDef [simp]
declare MinXDef [simp]
declare MinYDef [simp]
declare TO2 [simp]
declare TO4 [simp]
declare TO6 [simp]
declare IUO01 [simp]
declare IUO02 [simp]
declare IUO03 [simp]
declare IUO04 [simp]
declare IUO05 [simp]
declare IUO06 [simp]
declare IUO07 [simp]
declare IOO13 [simp]
declare IOO14 [simp]
declare IOO15 [simp]
declare IOO16 [simp]
declare IOO17 [simp]
declare IOO18 [simp]
declare IOO19 [simp]
declare IOO20 [simp]
declare IOO21 [simp]
declare IOO22 [simp]
declare IOO23 [simp]
declare IOO24 [simp]
declare IOO25 [simp]
declare IOO26 [simp]
declare IOO27 [simp]
declare IOO28 [simp]
declare IOO29 [simp]
declare IOO30 [simp]
declare IOO31 [simp]
declare IOO32 [simp]
declare IOO33 [simp]
declare IBO5 [simp]
declare IBO6 [simp]
declare IBO7 [simp]
declare IBO8 [simp]
declare IBO9 [simp]
declare IBO10 [simp]
declare IBO11 [simp]
declare IBO12 [simp]
declare NotDefHead [simp]
declare HeadDef [simp]
declare NotDefTail [simp]
declare TailDef [simp]
declare FoldrNil [simp]
declare FoldlNil [simp]
declare MapNil [simp]
declare XPlusXPlusNil [simp]
declare FilterNil [simp]
declare FilterConsF [simp]
declare ZipNil [simp]
declare UnzipNil [simp]
declare ILE01 [simp]
declare ILO01 [simp]
declare ILO02 [simp]
declare ILO03 [simp]
declare ILO04 [simp]
declare ILO05 [simp]
declare ILO06 [simp]
declare ILO11 [simp]
declare ILO12 [simp]
declare ILO13 [simp]
declare ILO14 [simp]
declare ILO15 [simp]
declare ILO16 [simp]
declare ILO17 [simp]
declare ILO18 [simp]
declare InitNil [simp]
declare InitConsNil [simp]
declare LastNil [simp]
declare LastConsNil [simp]
declare LastConsCons [simp]
declare NullNil [simp]
declare NullCons [simp]
declare ReverseNil [simp]
declare Foldr1Nil [simp]
declare Foldr1ConsNil [simp]
declare Foldl1Nil [simp]
declare Foldl1ConsNil [simp]
declare Scanl1Nil [simp]
declare Scanl1Cons [simp]
declare ScanrNil [simp]
declare Scanr1Nil [simp]
declare Scanr1ConsNil [simp]
declare ScanlProperty [simp]
declare ScanrProperty [simp]
declare MaximunNil [simp]
declare MinimunNil [simp]
declare TakeWhileNil [simp]
declare TakeWhileConsF [simp]
declare DropWhileNil [simp]
declare DropWhileConsT [simp]
declare DropWhileConsF [simp]
declare SpanNil [simp]
declare SpanThm [simp]
declare DeleteNil [simp]
declare DeleteConsT [simp]
declare SelectT [simp]
declare SelectF [simp]
declare ga_selector_pre [simp]
declare ga_selector_undef_pre_0 [simp]
declare ga_comm___XPlus__ [simp]
declare ga_assoc___XPlus__ [simp]
declare ga_right_unit___XPlus__ [simp]
declare ga_left_unit___XPlus__ [simp]
declare ga_left_comm___XPlus__ [simp]
declare ga_comm___Xx__ [simp]
declare ga_assoc___Xx__ [simp]
declare ga_right_unit___Xx__ [simp]
declare ga_left_unit___Xx__ [simp]
declare ga_left_comm___Xx__ [simp]
declare ga_comm_min [simp]
declare ga_assoc_min [simp]
declare ga_left_comm_min [simp]
declare ga_comm_max [simp]
declare ga_assoc_max [simp]
declare ga_right_unit_max [simp]
declare ga_left_unit_max [simp]
declare ga_left_comm_max [simp]
declare leq_def1_Nat [simp]
declare dvd_def_Nat [simp]
declare leq_def2_Nat [simp]
declare leq_def3_Nat [simp]
declare geq_def_Nat [simp]
declare less_def_Nat [simp]
declare greater_def_Nat [simp]
declare even_0_Nat [simp]
declare even_suc_Nat [simp]
declare odd_def_Nat [simp]
declare factorial_0 [simp]
declare factorial_suc [simp]
declare add_0_Nat [simp]
declare add_suc_Nat [simp]
declare mult_0_Nat [simp]
declare mult_suc_Nat [simp]
declare power_0_Nat [simp]
declare power_suc_Nat [simp]
declare subTotal_def1_Nat [simp]
declare subTotal_def2_Nat [simp]
declare sub_dom_Nat [simp]
declare divide_0_Nat [simp]
declare min_0 [simp]
declare ga_selector_ord [simp]
declare chr_ord_inverse [simp]
declare ga_comm___XPlus___80 [simp]
declare ga_assoc___XPlus___86 [simp]
declare ga_right_unit___XPlus___77 [simp]
declare ga_left_unit___XPlus___78 [simp]
declare ga_left_comm___XPlus___85 [simp]
declare ga_comm___Xx___79 [simp]
declare ga_assoc___Xx___84 [simp]
declare ga_right_unit___Xx___75 [simp]
declare ga_left_unit___Xx___76 [simp]
declare ga_left_comm___Xx___83 [simp]
declare ga_comm_min_82 [simp]
declare ga_comm_max_81 [simp]
declare ga_assoc_min_90 [simp]
declare ga_assoc_max_88 [simp]
declare ga_left_comm_min_89 [simp]
declare ga_left_comm_max_87 [simp]
declare leq_def_Int [simp]
declare even_def_Int [simp]
declare odd_alt_Int [simp]
declare neg_def_Int [simp]
declare sign_def_Int [simp]
declare abs_def_Int [simp]
declare add_def_Int [simp]
declare mult_def_Int [simp]
declare sub_def_Int [simp]
declare min_def_Int [simp]
declare max_def_Int [simp]
declare power_neg1_Int [simp]
declare power_others_Int [simp]
declare divide_Int [simp]
declare div_Int [simp]
declare quot_neg_Int [simp]
declare quot_nonneg_Int [simp]
declare quot_rem_Int [simp]
declare rem_nonneg_Int [simp]
declare mod_Int [simp]
declare Int_Nat_sub_compat [simp]
declare quot_abs_Int [simp]
declare rem_abs_Int [simp]
declare ga_comm___XPlus___139 [simp]
declare ga_assoc___XPlus___145 [simp]
declare ga_right_unit___XPlus___136 [simp]
declare ga_left_unit___XPlus___137 [simp]
declare ga_left_comm___XPlus___144 [simp]
declare ga_comm___Xx___138 [simp]
declare ga_assoc___Xx___143 [simp]
declare ga_right_unit___Xx___134 [simp]
declare ga_left_unit___Xx___135 [simp]
declare ga_left_comm___Xx___142 [simp]
declare ga_comm_min_141 [simp]
declare ga_comm_max_140 [simp]
declare ga_assoc_min_149 [simp]
declare ga_assoc_max_147 [simp]
declare ga_left_comm_min_148 [simp]
declare ga_left_comm_max_146 [simp]
declare divide_def1_Rat [simp]
declare power_0_Rat [simp]
declare AbsSignumLaw [simp]
declare IPN05 [simp]
declare IPN06 [simp]
declare INN01 [simp]
declare INN02 [simp]
declare INN03 [simp]
declare INN05 [simp]
declare IIN05 [simp]
declare IRN05 [simp]
declare ICE01 [simp]
declare ICE02 [simp]

theorem StringT1 :
"ALL (x :: Char partial).
 ALL (xs :: Char List partial).
 ALL (y :: Char partial). x ==' y --> X_Cons x xs ==' X_Cons y xs"
using X1_def_Nat X2_def_Nat X3_def_Nat X4_def_Nat X5_def_Nat
      X6_def_Nat X7_def_Nat X8_def_Nat X9_def_Nat decimal_def Pos_def
      X1_as_Pos_def slash_000 slash_001 slash_002 slash_003 slash_004
      slash_005 slash_006 slash_007 slash_008 slash_009 slash_010
      slash_011 slash_012 slash_013 slash_014 slash_015 slash_016
      slash_017 slash_018 slash_019 slash_020 slash_021 slash_022
      slash_023 slash_024 slash_025 slash_026 slash_027 slash_028
      slash_029 slash_030 slash_031 slash_032 slash_033 slash_034
      slash_035 slash_036 slash_037 slash_038 slash_039 slash_040
      slash_041 slash_042 slash_043 slash_044 slash_045 slash_046
      slash_047 slash_048 slash_049 slash_050 slash_051 slash_052
      slash_053 slash_054 slash_055 slash_056 slash_057 slash_058
      slash_059 slash_060 slash_061 slash_062 slash_063 slash_064
      slash_065 slash_066 slash_067 slash_068 slash_069 slash_070
      slash_071 slash_072 slash_073 slash_074 slash_075 slash_076
      slash_077 slash_078 slash_079 slash_080 slash_081 slash_082
      slash_083 slash_084 slash_085 slash_086 slash_087 slash_088
      slash_089 slash_090 slash_091 slash_092 slash_093 slash_094
      slash_095 slash_096 slash_097 slash_098 slash_099 slash_100
      slash_101 slash_102 slash_103 slash_104 slash_105 slash_106
      slash_107 slash_108 slash_109 slash_110 slash_111 slash_112
      slash_113 slash_114 slash_115 slash_116 slash_117 slash_118
      slash_119 slash_120 slash_121 slash_122 slash_123 slash_124
      slash_125 slash_126 slash_127 slash_128 slash_129 slash_130
      slash_131 slash_132 slash_133 slash_134 slash_135 slash_136
      slash_137 slash_138 slash_139 slash_140 slash_141 slash_142
      slash_143 slash_144 slash_145 slash_146 slash_147 slash_148
      slash_149 slash_150 slash_151 slash_152 slash_153 slash_154
      slash_155 slash_156 slash_157 slash_158 slash_159 slash_160
      slash_161 slash_162 slash_163 slash_164 slash_165 slash_166
      slash_167 slash_168 slash_169 slash_170 slash_171 slash_172
      slash_173 slash_174 slash_175 slash_176 slash_177 slash_178
      slash_179 slash_180 slash_181 slash_182 slash_183 slash_184
      slash_185 slash_186 slash_187 slash_188 slash_189 slash_190
      slash_191 slash_192 slash_193 slash_194 slash_195 slash_196
      slash_197 slash_198 slash_199 slash_200 slash_201 slash_202
      slash_203 slash_204 slash_205 slash_206 slash_207 slash_208
      slash_209 slash_210 slash_211 slash_212 slash_213 slash_214
      slash_215 slash_216 slash_217 slash_218 slash_219 slash_220
      slash_221 slash_222 slash_223 slash_224 slash_225 slash_226
      slash_227 slash_228 slash_229 slash_230 slash_231 slash_232
      slash_233 slash_234 slash_235 slash_236 slash_237 slash_238
      slash_239 slash_240 slash_241 slash_242 slash_243 slash_244
      slash_245 slash_246 slash_247 slash_248 slash_249 slash_250
      slash_251 slash_252 slash_253 slash_254 slash_255 printable_32
      printable_33 printable_34 printable_35 printable_36 printable_37
      printable_38 printable_39 printable_40 printable_41 printable_42
      printable_43 printable_44 printable_45 printable_46 printable_47
      printable_48 printable_49 printable_50 printable_51 printable_52
      printable_53 printable_54 printable_55 printable_56 printable_57
      printable_58 printable_59 printable_60 printable_61 printable_62
      printable_63 printable_64 printable_65 printable_66 printable_67
      printable_68 printable_69 printable_70 printable_71 printable_72
      printable_73 printable_74 printable_75 printable_76 printable_77
      printable_78 printable_79 printable_80 printable_81 printable_82
      printable_83 printable_84 printable_85 printable_86 printable_87
      printable_88 printable_89 printable_90 printable_91 printable_92
      printable_93 printable_94 printable_95 printable_96 printable_97
      printable_98 printable_99 printable_100 printable_101 printable_102
      printable_103 printable_104 printable_105 printable_106
      printable_107 printable_108 printable_109 printable_110
      printable_111 printable_112 printable_113 printable_114
      printable_115 printable_116 printable_117 printable_118
      printable_119 printable_120 printable_121 printable_122
      printable_123 printable_124 printable_125 printable_126
      printable_160 printable_161 printable_162 printable_163
      printable_164 printable_165 printable_166 printable_167
      printable_168 printable_169 printable_170 printable_171
      printable_172 printable_173 printable_174 printable_175
      printable_176 printable_177 printable_178 printable_179
      printable_180 printable_181 printable_182 printable_183
      printable_184 printable_185 printable_186 printable_187
      printable_188 printable_189 printable_190 printable_191
      printable_192 printable_193 printable_194 printable_195
      printable_196 printable_197 printable_198 printable_199
      printable_200 printable_201 printable_202 printable_203
      printable_204 printable_205 printable_206 printable_207
      printable_208 printable_209 printable_210 printable_211
      printable_212 printable_213 printable_214 printable_215
      printable_216 printable_217 printable_218 printable_219
      printable_220 printable_221 printable_222 printable_223
      printable_224 printable_225 printable_226 printable_227
      printable_228 printable_229 printable_230 printable_231
      printable_232 printable_233 printable_234 printable_235
      printable_236 printable_237 printable_238 printable_239
      printable_240 printable_241 printable_242 printable_243
      printable_244 printable_245 printable_246 printable_247
      printable_248 printable_249 printable_250 printable_251
      printable_252 printable_253 printable_254 printable_255
      isLetter_def isDigit_def isPrintable_def slash_o000 slash_o001
      slash_o002 slash_o003 slash_o004 slash_o005 slash_o006 slash_o007
      slash_o010 slash_o011 slash_o012 slash_o013 slash_o014 slash_o015
      slash_o016 slash_o017 slash_o020 slash_o021 slash_o022 slash_o023
      slash_o024 slash_o025 slash_o026 slash_o027 slash_o030 slash_o031
      slash_o032 slash_o033 slash_o034 slash_o035 slash_o036 slash_o037
      slash_o040 slash_o041 slash_o042 slash_o043 slash_o044 slash_o045
      slash_o046 slash_o047 slash_o050 slash_o051 slash_o052 slash_o053
      slash_o054 slash_o055 slash_o056 slash_o057 slash_o060 slash_o061
      slash_o062 slash_o063 slash_o064 slash_o065 slash_o066 slash_o067
      slash_o070 slash_o071 slash_o072 slash_o073 slash_o074 slash_o075
      slash_o076 slash_o077 slash_o100 slash_o101 slash_o102 slash_o103
      slash_o104 slash_o105 slash_o106 slash_o107 slash_o110 slash_o111
      slash_o112 slash_o113 slash_o114 slash_o115 slash_o116 slash_o117
      slash_o120 slash_o121 slash_o122 slash_o123 slash_o124 slash_o125
      slash_o126 slash_o127 slash_o130 slash_o131 slash_o132 slash_o133
      slash_o134 slash_o135 slash_o136 slash_o137 slash_o140 slash_o141
      slash_o142 slash_o143 slash_o144 slash_o145 slash_o146 slash_o147
      slash_o150 slash_o151 slash_o152 slash_o153 slash_o154 slash_o155
      slash_o156 slash_o157 slash_o160 slash_o161 slash_o162 slash_o163
      slash_o164 slash_o165 slash_o166 slash_o167 slash_o170 slash_o171
      slash_o172 slash_o173 slash_o174 slash_o175 slash_o176 slash_o177
      slash_o200 slash_o201 slash_o202 slash_o203 slash_o204 slash_o205
      slash_o206 slash_o207 slash_o210 slash_o211 slash_o212 slash_o213
      slash_o214 slash_o215 slash_o216 slash_o217 slash_o220 slash_o221
      slash_o222 slash_o223 slash_o224 slash_o225 slash_o226 slash_o227
      slash_o230 slash_o231 slash_o232 slash_o233 slash_o234 slash_o235
      slash_o236 slash_o237 slash_o240 slash_o241 slash_o242 slash_o243
      slash_o244 slash_o245 slash_o246 slash_o247 slash_o250 slash_o251
      slash_o252 slash_o253 slash_o254 slash_o255 slash_o256 slash_o257
      slash_o260 slash_o261 slash_o262 slash_o263 slash_o264 slash_o265
      slash_o266 slash_o267 slash_o270 slash_o271 slash_o272 slash_o273
      slash_o274 slash_o275 slash_o276 slash_o277 slash_o300 slash_o301
      slash_o302 slash_o303 slash_o304 slash_o305 slash_o306 slash_o307
      slash_o310 slash_o311 slash_o312 slash_o313 slash_o314 slash_o315
      slash_o316 slash_o317 slash_o320 slash_o321 slash_o322 slash_o323
      slash_o324 slash_o325 slash_o326 slash_o327 slash_o330 slash_o331
      slash_o332 slash_o333 slash_o334 slash_o335 slash_o336 slash_o337
      slash_o340 slash_o341 slash_o342 slash_o343 slash_o344 slash_o345
      slash_o346 slash_o347 slash_o350 slash_o351 slash_o352 slash_o353
      slash_o354 slash_o355 slash_o356 slash_o357 slash_o360 slash_o361
      slash_o362 slash_o363 slash_o364 slash_o365 slash_o366 slash_o367
      slash_o370 slash_o371 slash_o372 slash_o373 slash_o374 slash_o375
      slash_o376 slash_o377 slash_x00 slash_x01 slash_x02 slash_x03
      slash_x04 slash_x05 slash_x06 slash_x07 slash_x08 slash_x09
      slash_x0A slash_x0B slash_x0C slash_x0D slash_x0E slash_x0F
      slash_x10 slash_x11 slash_x12 slash_x13 slash_x14 slash_x15
      slash_x16 slash_x17 slash_x18 slash_x19 slash_x1A slash_x1B
      slash_x1C slash_x1D slash_x1E slash_x1F slash_x20 slash_x21
      slash_x22 slash_x23 slash_x24 slash_x25 slash_x26 slash_x27
      slash_x28 slash_x29 slash_x2A slash_x2B slash_x2C slash_x2D
      slash_x2E slash_x2F slash_x30 slash_x31 slash_x32 slash_x33
      slash_x34 slash_x35 slash_x36 slash_x37 slash_x38 slash_x39
      slash_x3A slash_x3B slash_x3C slash_x3D slash_x3E slash_x3F
      slash_x40 slash_x41 slash_x42 slash_x43 slash_x44 slash_x45
      slash_x46 slash_x47 slash_x48 slash_x49 slash_x4A slash_x4B
      slash_x4C slash_x4D slash_x4E slash_x4F slash_x50 slash_x51
      slash_x52 slash_x53 slash_x54 slash_x55 slash_x56 slash_x57
      slash_x58 slash_x59 slash_x5A slash_x5B slash_x5C slash_x5D
      slash_x5E slash_x5F slash_x60 slash_x61 slash_x62 slash_x63
      slash_x64 slash_x65 slash_x66 slash_x67 slash_x68 slash_x69
      slash_x6A slash_x6B slash_x6C slash_x6D slash_x6E slash_x6F
      slash_x70 slash_x71 slash_x72 slash_x73 slash_x74 slash_x75
      slash_x76 slash_x77 slash_x78 slash_x79 slash_x7A slash_x7B
      slash_x7C slash_x7D slash_x7E slash_x7F slash_x80 slash_x81
      slash_x82 slash_x83 slash_x84 slash_x85 slash_x86 slash_x87
      slash_x88 slash_x89 slash_x8A slash_x8B slash_x8C slash_x8D
      slash_x8E slash_x8F slash_x90 slash_x91 slash_x92 slash_x93
      slash_x94 slash_x95 slash_x96 slash_x97 slash_x98 slash_x99
      slash_x9A slash_x9B slash_x9C slash_x9D slash_x9E slash_x9F
      slash_xA0 slash_xA1 slash_xA2 slash_xA3 slash_xA4 slash_xA5
      slash_xA6 slash_xA7 slash_xA8 slash_xA9 slash_xAA slash_xAB
      slash_xAC slash_xAD slash_xAE slash_xAF slash_xB0 slash_xB1
      slash_xB2 slash_xB3 slash_xB4 slash_xB5 slash_xB6 slash_xB7
      slash_xB8 slash_xB9 slash_xBA slash_xBB slash_xBC slash_xBD
      slash_xBE slash_xBF slash_xC0 slash_xC1 slash_xC2 slash_xC3
      slash_xC4 slash_xC5 slash_xC6 slash_xC7 slash_xC8 slash_xC9
      slash_xCA slash_xCB slash_xCC slash_xCD slash_xCE slash_xCF
      slash_xD0 slash_xD1 slash_xD2 slash_xD3 slash_xD4 slash_xD5
      slash_xD6 slash_xD7 slash_xD8 slash_xD9 slash_xDA slash_xDB
      slash_xDC slash_xDD slash_xDE slash_xDF slash_xE0 slash_xE1
      slash_xE2 slash_xE3 slash_xE4 slash_xE5 slash_xE6 slash_xE7
      slash_xE8 slash_xE9 slash_xEA slash_xEB slash_xEC slash_xED
      slash_xEE slash_xEF slash_xF0 slash_xF1 slash_xF2 slash_xF3
      slash_xF4 slash_xF5 slash_xF6 slash_xF7 slash_xF8 slash_xF9
      slash_xFA slash_xFB slash_xFC slash_xFD slash_xFE slash_xFF NUL_def
      SOH_def SYX_def ETX_def EOT_def ENQ_def ACK_def BEL_def BS_def
      HT_def LF_def VT_def FF_def CR_def SO_def SI_def DLE_def DC1_def
      DC2_def DC3_def DC4_def NAK_def SYN_def ETB_def CAN_def EM_def
      SUB_def ESC_def FS_def GS_def RS_def US_def SP_def DEL_def NL_def
      NP_def slash_n slash_t slash_v slash_b slash_r slash_f slash_a
      slash_quest
by (auto)

ML "Header.record \"StringT1\""

theorem StringT2 :
"ALL (x :: Char partial).
 ALL (xs :: Char List partial).
 ALL (y :: Char partial).
 ALL (ys :: Char List partial).
 xs /= ys --> ~ X_Cons x ys ==' X_Cons y xs"
using X1_def_Nat X2_def_Nat X3_def_Nat X4_def_Nat X5_def_Nat
      X6_def_Nat X7_def_Nat X8_def_Nat X9_def_Nat decimal_def Pos_def
      X1_as_Pos_def slash_000 slash_001 slash_002 slash_003 slash_004
      slash_005 slash_006 slash_007 slash_008 slash_009 slash_010
      slash_011 slash_012 slash_013 slash_014 slash_015 slash_016
      slash_017 slash_018 slash_019 slash_020 slash_021 slash_022
      slash_023 slash_024 slash_025 slash_026 slash_027 slash_028
      slash_029 slash_030 slash_031 slash_032 slash_033 slash_034
      slash_035 slash_036 slash_037 slash_038 slash_039 slash_040
      slash_041 slash_042 slash_043 slash_044 slash_045 slash_046
      slash_047 slash_048 slash_049 slash_050 slash_051 slash_052
      slash_053 slash_054 slash_055 slash_056 slash_057 slash_058
      slash_059 slash_060 slash_061 slash_062 slash_063 slash_064
      slash_065 slash_066 slash_067 slash_068 slash_069 slash_070
      slash_071 slash_072 slash_073 slash_074 slash_075 slash_076
      slash_077 slash_078 slash_079 slash_080 slash_081 slash_082
      slash_083 slash_084 slash_085 slash_086 slash_087 slash_088
      slash_089 slash_090 slash_091 slash_092 slash_093 slash_094
      slash_095 slash_096 slash_097 slash_098 slash_099 slash_100
      slash_101 slash_102 slash_103 slash_104 slash_105 slash_106
      slash_107 slash_108 slash_109 slash_110 slash_111 slash_112
      slash_113 slash_114 slash_115 slash_116 slash_117 slash_118
      slash_119 slash_120 slash_121 slash_122 slash_123 slash_124
      slash_125 slash_126 slash_127 slash_128 slash_129 slash_130
      slash_131 slash_132 slash_133 slash_134 slash_135 slash_136
      slash_137 slash_138 slash_139 slash_140 slash_141 slash_142
      slash_143 slash_144 slash_145 slash_146 slash_147 slash_148
      slash_149 slash_150 slash_151 slash_152 slash_153 slash_154
      slash_155 slash_156 slash_157 slash_158 slash_159 slash_160
      slash_161 slash_162 slash_163 slash_164 slash_165 slash_166
      slash_167 slash_168 slash_169 slash_170 slash_171 slash_172
      slash_173 slash_174 slash_175 slash_176 slash_177 slash_178
      slash_179 slash_180 slash_181 slash_182 slash_183 slash_184
      slash_185 slash_186 slash_187 slash_188 slash_189 slash_190
      slash_191 slash_192 slash_193 slash_194 slash_195 slash_196
      slash_197 slash_198 slash_199 slash_200 slash_201 slash_202
      slash_203 slash_204 slash_205 slash_206 slash_207 slash_208
      slash_209 slash_210 slash_211 slash_212 slash_213 slash_214
      slash_215 slash_216 slash_217 slash_218 slash_219 slash_220
      slash_221 slash_222 slash_223 slash_224 slash_225 slash_226
      slash_227 slash_228 slash_229 slash_230 slash_231 slash_232
      slash_233 slash_234 slash_235 slash_236 slash_237 slash_238
      slash_239 slash_240 slash_241 slash_242 slash_243 slash_244
      slash_245 slash_246 slash_247 slash_248 slash_249 slash_250
      slash_251 slash_252 slash_253 slash_254 slash_255 printable_32
      printable_33 printable_34 printable_35 printable_36 printable_37
      printable_38 printable_39 printable_40 printable_41 printable_42
      printable_43 printable_44 printable_45 printable_46 printable_47
      printable_48 printable_49 printable_50 printable_51 printable_52
      printable_53 printable_54 printable_55 printable_56 printable_57
      printable_58 printable_59 printable_60 printable_61 printable_62
      printable_63 printable_64 printable_65 printable_66 printable_67
      printable_68 printable_69 printable_70 printable_71 printable_72
      printable_73 printable_74 printable_75 printable_76 printable_77
      printable_78 printable_79 printable_80 printable_81 printable_82
      printable_83 printable_84 printable_85 printable_86 printable_87
      printable_88 printable_89 printable_90 printable_91 printable_92
      printable_93 printable_94 printable_95 printable_96 printable_97
      printable_98 printable_99 printable_100 printable_101 printable_102
      printable_103 printable_104 printable_105 printable_106
      printable_107 printable_108 printable_109 printable_110
      printable_111 printable_112 printable_113 printable_114
      printable_115 printable_116 printable_117 printable_118
      printable_119 printable_120 printable_121 printable_122
      printable_123 printable_124 printable_125 printable_126
      printable_160 printable_161 printable_162 printable_163
      printable_164 printable_165 printable_166 printable_167
      printable_168 printable_169 printable_170 printable_171
      printable_172 printable_173 printable_174 printable_175
      printable_176 printable_177 printable_178 printable_179
      printable_180 printable_181 printable_182 printable_183
      printable_184 printable_185 printable_186 printable_187
      printable_188 printable_189 printable_190 printable_191
      printable_192 printable_193 printable_194 printable_195
      printable_196 printable_197 printable_198 printable_199
      printable_200 printable_201 printable_202 printable_203
      printable_204 printable_205 printable_206 printable_207
      printable_208 printable_209 printable_210 printable_211
      printable_212 printable_213 printable_214 printable_215
      printable_216 printable_217 printable_218 printable_219
      printable_220 printable_221 printable_222 printable_223
      printable_224 printable_225 printable_226 printable_227
      printable_228 printable_229 printable_230 printable_231
      printable_232 printable_233 printable_234 printable_235
      printable_236 printable_237 printable_238 printable_239
      printable_240 printable_241 printable_242 printable_243
      printable_244 printable_245 printable_246 printable_247
      printable_248 printable_249 printable_250 printable_251
      printable_252 printable_253 printable_254 printable_255
      isLetter_def isDigit_def isPrintable_def slash_o000 slash_o001
      slash_o002 slash_o003 slash_o004 slash_o005 slash_o006 slash_o007
      slash_o010 slash_o011 slash_o012 slash_o013 slash_o014 slash_o015
      slash_o016 slash_o017 slash_o020 slash_o021 slash_o022 slash_o023
      slash_o024 slash_o025 slash_o026 slash_o027 slash_o030 slash_o031
      slash_o032 slash_o033 slash_o034 slash_o035 slash_o036 slash_o037
      slash_o040 slash_o041 slash_o042 slash_o043 slash_o044 slash_o045
      slash_o046 slash_o047 slash_o050 slash_o051 slash_o052 slash_o053
      slash_o054 slash_o055 slash_o056 slash_o057 slash_o060 slash_o061
      slash_o062 slash_o063 slash_o064 slash_o065 slash_o066 slash_o067
      slash_o070 slash_o071 slash_o072 slash_o073 slash_o074 slash_o075
      slash_o076 slash_o077 slash_o100 slash_o101 slash_o102 slash_o103
      slash_o104 slash_o105 slash_o106 slash_o107 slash_o110 slash_o111
      slash_o112 slash_o113 slash_o114 slash_o115 slash_o116 slash_o117
      slash_o120 slash_o121 slash_o122 slash_o123 slash_o124 slash_o125
      slash_o126 slash_o127 slash_o130 slash_o131 slash_o132 slash_o133
      slash_o134 slash_o135 slash_o136 slash_o137 slash_o140 slash_o141
      slash_o142 slash_o143 slash_o144 slash_o145 slash_o146 slash_o147
      slash_o150 slash_o151 slash_o152 slash_o153 slash_o154 slash_o155
      slash_o156 slash_o157 slash_o160 slash_o161 slash_o162 slash_o163
      slash_o164 slash_o165 slash_o166 slash_o167 slash_o170 slash_o171
      slash_o172 slash_o173 slash_o174 slash_o175 slash_o176 slash_o177
      slash_o200 slash_o201 slash_o202 slash_o203 slash_o204 slash_o205
      slash_o206 slash_o207 slash_o210 slash_o211 slash_o212 slash_o213
      slash_o214 slash_o215 slash_o216 slash_o217 slash_o220 slash_o221
      slash_o222 slash_o223 slash_o224 slash_o225 slash_o226 slash_o227
      slash_o230 slash_o231 slash_o232 slash_o233 slash_o234 slash_o235
      slash_o236 slash_o237 slash_o240 slash_o241 slash_o242 slash_o243
      slash_o244 slash_o245 slash_o246 slash_o247 slash_o250 slash_o251
      slash_o252 slash_o253 slash_o254 slash_o255 slash_o256 slash_o257
      slash_o260 slash_o261 slash_o262 slash_o263 slash_o264 slash_o265
      slash_o266 slash_o267 slash_o270 slash_o271 slash_o272 slash_o273
      slash_o274 slash_o275 slash_o276 slash_o277 slash_o300 slash_o301
      slash_o302 slash_o303 slash_o304 slash_o305 slash_o306 slash_o307
      slash_o310 slash_o311 slash_o312 slash_o313 slash_o314 slash_o315
      slash_o316 slash_o317 slash_o320 slash_o321 slash_o322 slash_o323
      slash_o324 slash_o325 slash_o326 slash_o327 slash_o330 slash_o331
      slash_o332 slash_o333 slash_o334 slash_o335 slash_o336 slash_o337
      slash_o340 slash_o341 slash_o342 slash_o343 slash_o344 slash_o345
      slash_o346 slash_o347 slash_o350 slash_o351 slash_o352 slash_o353
      slash_o354 slash_o355 slash_o356 slash_o357 slash_o360 slash_o361
      slash_o362 slash_o363 slash_o364 slash_o365 slash_o366 slash_o367
      slash_o370 slash_o371 slash_o372 slash_o373 slash_o374 slash_o375
      slash_o376 slash_o377 slash_x00 slash_x01 slash_x02 slash_x03
      slash_x04 slash_x05 slash_x06 slash_x07 slash_x08 slash_x09
      slash_x0A slash_x0B slash_x0C slash_x0D slash_x0E slash_x0F
      slash_x10 slash_x11 slash_x12 slash_x13 slash_x14 slash_x15
      slash_x16 slash_x17 slash_x18 slash_x19 slash_x1A slash_x1B
      slash_x1C slash_x1D slash_x1E slash_x1F slash_x20 slash_x21
      slash_x22 slash_x23 slash_x24 slash_x25 slash_x26 slash_x27
      slash_x28 slash_x29 slash_x2A slash_x2B slash_x2C slash_x2D
      slash_x2E slash_x2F slash_x30 slash_x31 slash_x32 slash_x33
      slash_x34 slash_x35 slash_x36 slash_x37 slash_x38 slash_x39
      slash_x3A slash_x3B slash_x3C slash_x3D slash_x3E slash_x3F
      slash_x40 slash_x41 slash_x42 slash_x43 slash_x44 slash_x45
      slash_x46 slash_x47 slash_x48 slash_x49 slash_x4A slash_x4B
      slash_x4C slash_x4D slash_x4E slash_x4F slash_x50 slash_x51
      slash_x52 slash_x53 slash_x54 slash_x55 slash_x56 slash_x57
      slash_x58 slash_x59 slash_x5A slash_x5B slash_x5C slash_x5D
      slash_x5E slash_x5F slash_x60 slash_x61 slash_x62 slash_x63
      slash_x64 slash_x65 slash_x66 slash_x67 slash_x68 slash_x69
      slash_x6A slash_x6B slash_x6C slash_x6D slash_x6E slash_x6F
      slash_x70 slash_x71 slash_x72 slash_x73 slash_x74 slash_x75
      slash_x76 slash_x77 slash_x78 slash_x79 slash_x7A slash_x7B
      slash_x7C slash_x7D slash_x7E slash_x7F slash_x80 slash_x81
      slash_x82 slash_x83 slash_x84 slash_x85 slash_x86 slash_x87
      slash_x88 slash_x89 slash_x8A slash_x8B slash_x8C slash_x8D
      slash_x8E slash_x8F slash_x90 slash_x91 slash_x92 slash_x93
      slash_x94 slash_x95 slash_x96 slash_x97 slash_x98 slash_x99
      slash_x9A slash_x9B slash_x9C slash_x9D slash_x9E slash_x9F
      slash_xA0 slash_xA1 slash_xA2 slash_xA3 slash_xA4 slash_xA5
      slash_xA6 slash_xA7 slash_xA8 slash_xA9 slash_xAA slash_xAB
      slash_xAC slash_xAD slash_xAE slash_xAF slash_xB0 slash_xB1
      slash_xB2 slash_xB3 slash_xB4 slash_xB5 slash_xB6 slash_xB7
      slash_xB8 slash_xB9 slash_xBA slash_xBB slash_xBC slash_xBD
      slash_xBE slash_xBF slash_xC0 slash_xC1 slash_xC2 slash_xC3
      slash_xC4 slash_xC5 slash_xC6 slash_xC7 slash_xC8 slash_xC9
      slash_xCA slash_xCB slash_xCC slash_xCD slash_xCE slash_xCF
      slash_xD0 slash_xD1 slash_xD2 slash_xD3 slash_xD4 slash_xD5
      slash_xD6 slash_xD7 slash_xD8 slash_xD9 slash_xDA slash_xDB
      slash_xDC slash_xDD slash_xDE slash_xDF slash_xE0 slash_xE1
      slash_xE2 slash_xE3 slash_xE4 slash_xE5 slash_xE6 slash_xE7
      slash_xE8 slash_xE9 slash_xEA slash_xEB slash_xEC slash_xED
      slash_xEE slash_xEF slash_xF0 slash_xF1 slash_xF2 slash_xF3
      slash_xF4 slash_xF5 slash_xF6 slash_xF7 slash_xF8 slash_xF9
      slash_xFA slash_xFB slash_xFC slash_xFD slash_xFE slash_xFF NUL_def
      SOH_def SYX_def ETX_def EOT_def ENQ_def ACK_def BEL_def BS_def
      HT_def LF_def VT_def FF_def CR_def SO_def SI_def DLE_def DC1_def
      DC2_def DC3_def DC4_def NAK_def SYN_def ETB_def CAN_def EM_def
      SUB_def ESC_def FS_def GS_def RS_def US_def SP_def DEL_def NL_def
      NP_def slash_n slash_t slash_v slash_b slash_r slash_f slash_a
      slash_quest
by (auto)

ML "Header.record \"StringT2\""

theorem StringT3 :
"ALL (a :: Char List partial).
 ALL (b :: Char List partial). a /= b --> ~ a ==' b"
using X1_def_Nat X2_def_Nat X3_def_Nat X4_def_Nat X5_def_Nat
      X6_def_Nat X7_def_Nat X8_def_Nat X9_def_Nat decimal_def Pos_def
      X1_as_Pos_def slash_000 slash_001 slash_002 slash_003 slash_004
      slash_005 slash_006 slash_007 slash_008 slash_009 slash_010
      slash_011 slash_012 slash_013 slash_014 slash_015 slash_016
      slash_017 slash_018 slash_019 slash_020 slash_021 slash_022
      slash_023 slash_024 slash_025 slash_026 slash_027 slash_028
      slash_029 slash_030 slash_031 slash_032 slash_033 slash_034
      slash_035 slash_036 slash_037 slash_038 slash_039 slash_040
      slash_041 slash_042 slash_043 slash_044 slash_045 slash_046
      slash_047 slash_048 slash_049 slash_050 slash_051 slash_052
      slash_053 slash_054 slash_055 slash_056 slash_057 slash_058
      slash_059 slash_060 slash_061 slash_062 slash_063 slash_064
      slash_065 slash_066 slash_067 slash_068 slash_069 slash_070
      slash_071 slash_072 slash_073 slash_074 slash_075 slash_076
      slash_077 slash_078 slash_079 slash_080 slash_081 slash_082
      slash_083 slash_084 slash_085 slash_086 slash_087 slash_088
      slash_089 slash_090 slash_091 slash_092 slash_093 slash_094
      slash_095 slash_096 slash_097 slash_098 slash_099 slash_100
      slash_101 slash_102 slash_103 slash_104 slash_105 slash_106
      slash_107 slash_108 slash_109 slash_110 slash_111 slash_112
      slash_113 slash_114 slash_115 slash_116 slash_117 slash_118
      slash_119 slash_120 slash_121 slash_122 slash_123 slash_124
      slash_125 slash_126 slash_127 slash_128 slash_129 slash_130
      slash_131 slash_132 slash_133 slash_134 slash_135 slash_136
      slash_137 slash_138 slash_139 slash_140 slash_141 slash_142
      slash_143 slash_144 slash_145 slash_146 slash_147 slash_148
      slash_149 slash_150 slash_151 slash_152 slash_153 slash_154
      slash_155 slash_156 slash_157 slash_158 slash_159 slash_160
      slash_161 slash_162 slash_163 slash_164 slash_165 slash_166
      slash_167 slash_168 slash_169 slash_170 slash_171 slash_172
      slash_173 slash_174 slash_175 slash_176 slash_177 slash_178
      slash_179 slash_180 slash_181 slash_182 slash_183 slash_184
      slash_185 slash_186 slash_187 slash_188 slash_189 slash_190
      slash_191 slash_192 slash_193 slash_194 slash_195 slash_196
      slash_197 slash_198 slash_199 slash_200 slash_201 slash_202
      slash_203 slash_204 slash_205 slash_206 slash_207 slash_208
      slash_209 slash_210 slash_211 slash_212 slash_213 slash_214
      slash_215 slash_216 slash_217 slash_218 slash_219 slash_220
      slash_221 slash_222 slash_223 slash_224 slash_225 slash_226
      slash_227 slash_228 slash_229 slash_230 slash_231 slash_232
      slash_233 slash_234 slash_235 slash_236 slash_237 slash_238
      slash_239 slash_240 slash_241 slash_242 slash_243 slash_244
      slash_245 slash_246 slash_247 slash_248 slash_249 slash_250
      slash_251 slash_252 slash_253 slash_254 slash_255 printable_32
      printable_33 printable_34 printable_35 printable_36 printable_37
      printable_38 printable_39 printable_40 printable_41 printable_42
      printable_43 printable_44 printable_45 printable_46 printable_47
      printable_48 printable_49 printable_50 printable_51 printable_52
      printable_53 printable_54 printable_55 printable_56 printable_57
      printable_58 printable_59 printable_60 printable_61 printable_62
      printable_63 printable_64 printable_65 printable_66 printable_67
      printable_68 printable_69 printable_70 printable_71 printable_72
      printable_73 printable_74 printable_75 printable_76 printable_77
      printable_78 printable_79 printable_80 printable_81 printable_82
      printable_83 printable_84 printable_85 printable_86 printable_87
      printable_88 printable_89 printable_90 printable_91 printable_92
      printable_93 printable_94 printable_95 printable_96 printable_97
      printable_98 printable_99 printable_100 printable_101 printable_102
      printable_103 printable_104 printable_105 printable_106
      printable_107 printable_108 printable_109 printable_110
      printable_111 printable_112 printable_113 printable_114
      printable_115 printable_116 printable_117 printable_118
      printable_119 printable_120 printable_121 printable_122
      printable_123 printable_124 printable_125 printable_126
      printable_160 printable_161 printable_162 printable_163
      printable_164 printable_165 printable_166 printable_167
      printable_168 printable_169 printable_170 printable_171
      printable_172 printable_173 printable_174 printable_175
      printable_176 printable_177 printable_178 printable_179
      printable_180 printable_181 printable_182 printable_183
      printable_184 printable_185 printable_186 printable_187
      printable_188 printable_189 printable_190 printable_191
      printable_192 printable_193 printable_194 printable_195
      printable_196 printable_197 printable_198 printable_199
      printable_200 printable_201 printable_202 printable_203
      printable_204 printable_205 printable_206 printable_207
      printable_208 printable_209 printable_210 printable_211
      printable_212 printable_213 printable_214 printable_215
      printable_216 printable_217 printable_218 printable_219
      printable_220 printable_221 printable_222 printable_223
      printable_224 printable_225 printable_226 printable_227
      printable_228 printable_229 printable_230 printable_231
      printable_232 printable_233 printable_234 printable_235
      printable_236 printable_237 printable_238 printable_239
      printable_240 printable_241 printable_242 printable_243
      printable_244 printable_245 printable_246 printable_247
      printable_248 printable_249 printable_250 printable_251
      printable_252 printable_253 printable_254 printable_255
      isLetter_def isDigit_def isPrintable_def slash_o000 slash_o001
      slash_o002 slash_o003 slash_o004 slash_o005 slash_o006 slash_o007
      slash_o010 slash_o011 slash_o012 slash_o013 slash_o014 slash_o015
      slash_o016 slash_o017 slash_o020 slash_o021 slash_o022 slash_o023
      slash_o024 slash_o025 slash_o026 slash_o027 slash_o030 slash_o031
      slash_o032 slash_o033 slash_o034 slash_o035 slash_o036 slash_o037
      slash_o040 slash_o041 slash_o042 slash_o043 slash_o044 slash_o045
      slash_o046 slash_o047 slash_o050 slash_o051 slash_o052 slash_o053
      slash_o054 slash_o055 slash_o056 slash_o057 slash_o060 slash_o061
      slash_o062 slash_o063 slash_o064 slash_o065 slash_o066 slash_o067
      slash_o070 slash_o071 slash_o072 slash_o073 slash_o074 slash_o075
      slash_o076 slash_o077 slash_o100 slash_o101 slash_o102 slash_o103
      slash_o104 slash_o105 slash_o106 slash_o107 slash_o110 slash_o111
      slash_o112 slash_o113 slash_o114 slash_o115 slash_o116 slash_o117
      slash_o120 slash_o121 slash_o122 slash_o123 slash_o124 slash_o125
      slash_o126 slash_o127 slash_o130 slash_o131 slash_o132 slash_o133
      slash_o134 slash_o135 slash_o136 slash_o137 slash_o140 slash_o141
      slash_o142 slash_o143 slash_o144 slash_o145 slash_o146 slash_o147
      slash_o150 slash_o151 slash_o152 slash_o153 slash_o154 slash_o155
      slash_o156 slash_o157 slash_o160 slash_o161 slash_o162 slash_o163
      slash_o164 slash_o165 slash_o166 slash_o167 slash_o170 slash_o171
      slash_o172 slash_o173 slash_o174 slash_o175 slash_o176 slash_o177
      slash_o200 slash_o201 slash_o202 slash_o203 slash_o204 slash_o205
      slash_o206 slash_o207 slash_o210 slash_o211 slash_o212 slash_o213
      slash_o214 slash_o215 slash_o216 slash_o217 slash_o220 slash_o221
      slash_o222 slash_o223 slash_o224 slash_o225 slash_o226 slash_o227
      slash_o230 slash_o231 slash_o232 slash_o233 slash_o234 slash_o235
      slash_o236 slash_o237 slash_o240 slash_o241 slash_o242 slash_o243
      slash_o244 slash_o245 slash_o246 slash_o247 slash_o250 slash_o251
      slash_o252 slash_o253 slash_o254 slash_o255 slash_o256 slash_o257
      slash_o260 slash_o261 slash_o262 slash_o263 slash_o264 slash_o265
      slash_o266 slash_o267 slash_o270 slash_o271 slash_o272 slash_o273
      slash_o274 slash_o275 slash_o276 slash_o277 slash_o300 slash_o301
      slash_o302 slash_o303 slash_o304 slash_o305 slash_o306 slash_o307
      slash_o310 slash_o311 slash_o312 slash_o313 slash_o314 slash_o315
      slash_o316 slash_o317 slash_o320 slash_o321 slash_o322 slash_o323
      slash_o324 slash_o325 slash_o326 slash_o327 slash_o330 slash_o331
      slash_o332 slash_o333 slash_o334 slash_o335 slash_o336 slash_o337
      slash_o340 slash_o341 slash_o342 slash_o343 slash_o344 slash_o345
      slash_o346 slash_o347 slash_o350 slash_o351 slash_o352 slash_o353
      slash_o354 slash_o355 slash_o356 slash_o357 slash_o360 slash_o361
      slash_o362 slash_o363 slash_o364 slash_o365 slash_o366 slash_o367
      slash_o370 slash_o371 slash_o372 slash_o373 slash_o374 slash_o375
      slash_o376 slash_o377 slash_x00 slash_x01 slash_x02 slash_x03
      slash_x04 slash_x05 slash_x06 slash_x07 slash_x08 slash_x09
      slash_x0A slash_x0B slash_x0C slash_x0D slash_x0E slash_x0F
      slash_x10 slash_x11 slash_x12 slash_x13 slash_x14 slash_x15
      slash_x16 slash_x17 slash_x18 slash_x19 slash_x1A slash_x1B
      slash_x1C slash_x1D slash_x1E slash_x1F slash_x20 slash_x21
      slash_x22 slash_x23 slash_x24 slash_x25 slash_x26 slash_x27
      slash_x28 slash_x29 slash_x2A slash_x2B slash_x2C slash_x2D
      slash_x2E slash_x2F slash_x30 slash_x31 slash_x32 slash_x33
      slash_x34 slash_x35 slash_x36 slash_x37 slash_x38 slash_x39
      slash_x3A slash_x3B slash_x3C slash_x3D slash_x3E slash_x3F
      slash_x40 slash_x41 slash_x42 slash_x43 slash_x44 slash_x45
      slash_x46 slash_x47 slash_x48 slash_x49 slash_x4A slash_x4B
      slash_x4C slash_x4D slash_x4E slash_x4F slash_x50 slash_x51
      slash_x52 slash_x53 slash_x54 slash_x55 slash_x56 slash_x57
      slash_x58 slash_x59 slash_x5A slash_x5B slash_x5C slash_x5D
      slash_x5E slash_x5F slash_x60 slash_x61 slash_x62 slash_x63
      slash_x64 slash_x65 slash_x66 slash_x67 slash_x68 slash_x69
      slash_x6A slash_x6B slash_x6C slash_x6D slash_x6E slash_x6F
      slash_x70 slash_x71 slash_x72 slash_x73 slash_x74 slash_x75
      slash_x76 slash_x77 slash_x78 slash_x79 slash_x7A slash_x7B
      slash_x7C slash_x7D slash_x7E slash_x7F slash_x80 slash_x81
      slash_x82 slash_x83 slash_x84 slash_x85 slash_x86 slash_x87
      slash_x88 slash_x89 slash_x8A slash_x8B slash_x8C slash_x8D
      slash_x8E slash_x8F slash_x90 slash_x91 slash_x92 slash_x93
      slash_x94 slash_x95 slash_x96 slash_x97 slash_x98 slash_x99
      slash_x9A slash_x9B slash_x9C slash_x9D slash_x9E slash_x9F
      slash_xA0 slash_xA1 slash_xA2 slash_xA3 slash_xA4 slash_xA5
      slash_xA6 slash_xA7 slash_xA8 slash_xA9 slash_xAA slash_xAB
      slash_xAC slash_xAD slash_xAE slash_xAF slash_xB0 slash_xB1
      slash_xB2 slash_xB3 slash_xB4 slash_xB5 slash_xB6 slash_xB7
      slash_xB8 slash_xB9 slash_xBA slash_xBB slash_xBC slash_xBD
      slash_xBE slash_xBF slash_xC0 slash_xC1 slash_xC2 slash_xC3
      slash_xC4 slash_xC5 slash_xC6 slash_xC7 slash_xC8 slash_xC9
      slash_xCA slash_xCB slash_xCC slash_xCD slash_xCE slash_xCF
      slash_xD0 slash_xD1 slash_xD2 slash_xD3 slash_xD4 slash_xD5
      slash_xD6 slash_xD7 slash_xD8 slash_xD9 slash_xDA slash_xDB
      slash_xDC slash_xDD slash_xDE slash_xDF slash_xE0 slash_xE1
      slash_xE2 slash_xE3 slash_xE4 slash_xE5 slash_xE6 slash_xE7
      slash_xE8 slash_xE9 slash_xEA slash_xEB slash_xEC slash_xED
      slash_xEE slash_xEF slash_xF0 slash_xF1 slash_xF2 slash_xF3
      slash_xF4 slash_xF5 slash_xF6 slash_xF7 slash_xF8 slash_xF9
      slash_xFA slash_xFB slash_xFC slash_xFD slash_xFE slash_xFF NUL_def
      SOH_def SYX_def ETX_def EOT_def ENQ_def ACK_def BEL_def BS_def
      HT_def LF_def VT_def FF_def CR_def SO_def SI_def DLE_def DC1_def
      DC2_def DC3_def DC4_def NAK_def SYN_def ETB_def CAN_def EM_def
      SUB_def ESC_def FS_def GS_def RS_def US_def SP_def DEL_def NL_def
      NP_def slash_n slash_t slash_v slash_b slash_r slash_f slash_a
      slash_quest
by (auto)

ML "Header.record \"StringT3\""

theorem StringT4 :
"ALL (x :: Char partial).
 ALL (xs :: Char List partial).
 ALL (y :: Char partial). x <_4 y --> X_Cons x xs <_4 X_Cons y xs"
using X1_def_Nat X2_def_Nat X3_def_Nat X4_def_Nat X5_def_Nat
      X6_def_Nat X7_def_Nat X8_def_Nat X9_def_Nat decimal_def Pos_def
      X1_as_Pos_def slash_000 slash_001 slash_002 slash_003 slash_004
      slash_005 slash_006 slash_007 slash_008 slash_009 slash_010
      slash_011 slash_012 slash_013 slash_014 slash_015 slash_016
      slash_017 slash_018 slash_019 slash_020 slash_021 slash_022
      slash_023 slash_024 slash_025 slash_026 slash_027 slash_028
      slash_029 slash_030 slash_031 slash_032 slash_033 slash_034
      slash_035 slash_036 slash_037 slash_038 slash_039 slash_040
      slash_041 slash_042 slash_043 slash_044 slash_045 slash_046
      slash_047 slash_048 slash_049 slash_050 slash_051 slash_052
      slash_053 slash_054 slash_055 slash_056 slash_057 slash_058
      slash_059 slash_060 slash_061 slash_062 slash_063 slash_064
      slash_065 slash_066 slash_067 slash_068 slash_069 slash_070
      slash_071 slash_072 slash_073 slash_074 slash_075 slash_076
      slash_077 slash_078 slash_079 slash_080 slash_081 slash_082
      slash_083 slash_084 slash_085 slash_086 slash_087 slash_088
      slash_089 slash_090 slash_091 slash_092 slash_093 slash_094
      slash_095 slash_096 slash_097 slash_098 slash_099 slash_100
      slash_101 slash_102 slash_103 slash_104 slash_105 slash_106
      slash_107 slash_108 slash_109 slash_110 slash_111 slash_112
      slash_113 slash_114 slash_115 slash_116 slash_117 slash_118
      slash_119 slash_120 slash_121 slash_122 slash_123 slash_124
      slash_125 slash_126 slash_127 slash_128 slash_129 slash_130
      slash_131 slash_132 slash_133 slash_134 slash_135 slash_136
      slash_137 slash_138 slash_139 slash_140 slash_141 slash_142
      slash_143 slash_144 slash_145 slash_146 slash_147 slash_148
      slash_149 slash_150 slash_151 slash_152 slash_153 slash_154
      slash_155 slash_156 slash_157 slash_158 slash_159 slash_160
      slash_161 slash_162 slash_163 slash_164 slash_165 slash_166
      slash_167 slash_168 slash_169 slash_170 slash_171 slash_172
      slash_173 slash_174 slash_175 slash_176 slash_177 slash_178
      slash_179 slash_180 slash_181 slash_182 slash_183 slash_184
      slash_185 slash_186 slash_187 slash_188 slash_189 slash_190
      slash_191 slash_192 slash_193 slash_194 slash_195 slash_196
      slash_197 slash_198 slash_199 slash_200 slash_201 slash_202
      slash_203 slash_204 slash_205 slash_206 slash_207 slash_208
      slash_209 slash_210 slash_211 slash_212 slash_213 slash_214
      slash_215 slash_216 slash_217 slash_218 slash_219 slash_220
      slash_221 slash_222 slash_223 slash_224 slash_225 slash_226
      slash_227 slash_228 slash_229 slash_230 slash_231 slash_232
      slash_233 slash_234 slash_235 slash_236 slash_237 slash_238
      slash_239 slash_240 slash_241 slash_242 slash_243 slash_244
      slash_245 slash_246 slash_247 slash_248 slash_249 slash_250
      slash_251 slash_252 slash_253 slash_254 slash_255 printable_32
      printable_33 printable_34 printable_35 printable_36 printable_37
      printable_38 printable_39 printable_40 printable_41 printable_42
      printable_43 printable_44 printable_45 printable_46 printable_47
      printable_48 printable_49 printable_50 printable_51 printable_52
      printable_53 printable_54 printable_55 printable_56 printable_57
      printable_58 printable_59 printable_60 printable_61 printable_62
      printable_63 printable_64 printable_65 printable_66 printable_67
      printable_68 printable_69 printable_70 printable_71 printable_72
      printable_73 printable_74 printable_75 printable_76 printable_77
      printable_78 printable_79 printable_80 printable_81 printable_82
      printable_83 printable_84 printable_85 printable_86 printable_87
      printable_88 printable_89 printable_90 printable_91 printable_92
      printable_93 printable_94 printable_95 printable_96 printable_97
      printable_98 printable_99 printable_100 printable_101 printable_102
      printable_103 printable_104 printable_105 printable_106
      printable_107 printable_108 printable_109 printable_110
      printable_111 printable_112 printable_113 printable_114
      printable_115 printable_116 printable_117 printable_118
      printable_119 printable_120 printable_121 printable_122
      printable_123 printable_124 printable_125 printable_126
      printable_160 printable_161 printable_162 printable_163
      printable_164 printable_165 printable_166 printable_167
      printable_168 printable_169 printable_170 printable_171
      printable_172 printable_173 printable_174 printable_175
      printable_176 printable_177 printable_178 printable_179
      printable_180 printable_181 printable_182 printable_183
      printable_184 printable_185 printable_186 printable_187
      printable_188 printable_189 printable_190 printable_191
      printable_192 printable_193 printable_194 printable_195
      printable_196 printable_197 printable_198 printable_199
      printable_200 printable_201 printable_202 printable_203
      printable_204 printable_205 printable_206 printable_207
      printable_208 printable_209 printable_210 printable_211
      printable_212 printable_213 printable_214 printable_215
      printable_216 printable_217 printable_218 printable_219
      printable_220 printable_221 printable_222 printable_223
      printable_224 printable_225 printable_226 printable_227
      printable_228 printable_229 printable_230 printable_231
      printable_232 printable_233 printable_234 printable_235
      printable_236 printable_237 printable_238 printable_239
      printable_240 printable_241 printable_242 printable_243
      printable_244 printable_245 printable_246 printable_247
      printable_248 printable_249 printable_250 printable_251
      printable_252 printable_253 printable_254 printable_255
      isLetter_def isDigit_def isPrintable_def slash_o000 slash_o001
      slash_o002 slash_o003 slash_o004 slash_o005 slash_o006 slash_o007
      slash_o010 slash_o011 slash_o012 slash_o013 slash_o014 slash_o015
      slash_o016 slash_o017 slash_o020 slash_o021 slash_o022 slash_o023
      slash_o024 slash_o025 slash_o026 slash_o027 slash_o030 slash_o031
      slash_o032 slash_o033 slash_o034 slash_o035 slash_o036 slash_o037
      slash_o040 slash_o041 slash_o042 slash_o043 slash_o044 slash_o045
      slash_o046 slash_o047 slash_o050 slash_o051 slash_o052 slash_o053
      slash_o054 slash_o055 slash_o056 slash_o057 slash_o060 slash_o061
      slash_o062 slash_o063 slash_o064 slash_o065 slash_o066 slash_o067
      slash_o070 slash_o071 slash_o072 slash_o073 slash_o074 slash_o075
      slash_o076 slash_o077 slash_o100 slash_o101 slash_o102 slash_o103
      slash_o104 slash_o105 slash_o106 slash_o107 slash_o110 slash_o111
      slash_o112 slash_o113 slash_o114 slash_o115 slash_o116 slash_o117
      slash_o120 slash_o121 slash_o122 slash_o123 slash_o124 slash_o125
      slash_o126 slash_o127 slash_o130 slash_o131 slash_o132 slash_o133
      slash_o134 slash_o135 slash_o136 slash_o137 slash_o140 slash_o141
      slash_o142 slash_o143 slash_o144 slash_o145 slash_o146 slash_o147
      slash_o150 slash_o151 slash_o152 slash_o153 slash_o154 slash_o155
      slash_o156 slash_o157 slash_o160 slash_o161 slash_o162 slash_o163
      slash_o164 slash_o165 slash_o166 slash_o167 slash_o170 slash_o171
      slash_o172 slash_o173 slash_o174 slash_o175 slash_o176 slash_o177
      slash_o200 slash_o201 slash_o202 slash_o203 slash_o204 slash_o205
      slash_o206 slash_o207 slash_o210 slash_o211 slash_o212 slash_o213
      slash_o214 slash_o215 slash_o216 slash_o217 slash_o220 slash_o221
      slash_o222 slash_o223 slash_o224 slash_o225 slash_o226 slash_o227
      slash_o230 slash_o231 slash_o232 slash_o233 slash_o234 slash_o235
      slash_o236 slash_o237 slash_o240 slash_o241 slash_o242 slash_o243
      slash_o244 slash_o245 slash_o246 slash_o247 slash_o250 slash_o251
      slash_o252 slash_o253 slash_o254 slash_o255 slash_o256 slash_o257
      slash_o260 slash_o261 slash_o262 slash_o263 slash_o264 slash_o265
      slash_o266 slash_o267 slash_o270 slash_o271 slash_o272 slash_o273
      slash_o274 slash_o275 slash_o276 slash_o277 slash_o300 slash_o301
      slash_o302 slash_o303 slash_o304 slash_o305 slash_o306 slash_o307
      slash_o310 slash_o311 slash_o312 slash_o313 slash_o314 slash_o315
      slash_o316 slash_o317 slash_o320 slash_o321 slash_o322 slash_o323
      slash_o324 slash_o325 slash_o326 slash_o327 slash_o330 slash_o331
      slash_o332 slash_o333 slash_o334 slash_o335 slash_o336 slash_o337
      slash_o340 slash_o341 slash_o342 slash_o343 slash_o344 slash_o345
      slash_o346 slash_o347 slash_o350 slash_o351 slash_o352 slash_o353
      slash_o354 slash_o355 slash_o356 slash_o357 slash_o360 slash_o361
      slash_o362 slash_o363 slash_o364 slash_o365 slash_o366 slash_o367
      slash_o370 slash_o371 slash_o372 slash_o373 slash_o374 slash_o375
      slash_o376 slash_o377 slash_x00 slash_x01 slash_x02 slash_x03
      slash_x04 slash_x05 slash_x06 slash_x07 slash_x08 slash_x09
      slash_x0A slash_x0B slash_x0C slash_x0D slash_x0E slash_x0F
      slash_x10 slash_x11 slash_x12 slash_x13 slash_x14 slash_x15
      slash_x16 slash_x17 slash_x18 slash_x19 slash_x1A slash_x1B
      slash_x1C slash_x1D slash_x1E slash_x1F slash_x20 slash_x21
      slash_x22 slash_x23 slash_x24 slash_x25 slash_x26 slash_x27
      slash_x28 slash_x29 slash_x2A slash_x2B slash_x2C slash_x2D
      slash_x2E slash_x2F slash_x30 slash_x31 slash_x32 slash_x33
      slash_x34 slash_x35 slash_x36 slash_x37 slash_x38 slash_x39
      slash_x3A slash_x3B slash_x3C slash_x3D slash_x3E slash_x3F
      slash_x40 slash_x41 slash_x42 slash_x43 slash_x44 slash_x45
      slash_x46 slash_x47 slash_x48 slash_x49 slash_x4A slash_x4B
      slash_x4C slash_x4D slash_x4E slash_x4F slash_x50 slash_x51
      slash_x52 slash_x53 slash_x54 slash_x55 slash_x56 slash_x57
      slash_x58 slash_x59 slash_x5A slash_x5B slash_x5C slash_x5D
      slash_x5E slash_x5F slash_x60 slash_x61 slash_x62 slash_x63
      slash_x64 slash_x65 slash_x66 slash_x67 slash_x68 slash_x69
      slash_x6A slash_x6B slash_x6C slash_x6D slash_x6E slash_x6F
      slash_x70 slash_x71 slash_x72 slash_x73 slash_x74 slash_x75
      slash_x76 slash_x77 slash_x78 slash_x79 slash_x7A slash_x7B
      slash_x7C slash_x7D slash_x7E slash_x7F slash_x80 slash_x81
      slash_x82 slash_x83 slash_x84 slash_x85 slash_x86 slash_x87
      slash_x88 slash_x89 slash_x8A slash_x8B slash_x8C slash_x8D
      slash_x8E slash_x8F slash_x90 slash_x91 slash_x92 slash_x93
      slash_x94 slash_x95 slash_x96 slash_x97 slash_x98 slash_x99
      slash_x9A slash_x9B slash_x9C slash_x9D slash_x9E slash_x9F
      slash_xA0 slash_xA1 slash_xA2 slash_xA3 slash_xA4 slash_xA5
      slash_xA6 slash_xA7 slash_xA8 slash_xA9 slash_xAA slash_xAB
      slash_xAC slash_xAD slash_xAE slash_xAF slash_xB0 slash_xB1
      slash_xB2 slash_xB3 slash_xB4 slash_xB5 slash_xB6 slash_xB7
      slash_xB8 slash_xB9 slash_xBA slash_xBB slash_xBC slash_xBD
      slash_xBE slash_xBF slash_xC0 slash_xC1 slash_xC2 slash_xC3
      slash_xC4 slash_xC5 slash_xC6 slash_xC7 slash_xC8 slash_xC9
      slash_xCA slash_xCB slash_xCC slash_xCD slash_xCE slash_xCF
      slash_xD0 slash_xD1 slash_xD2 slash_xD3 slash_xD4 slash_xD5
      slash_xD6 slash_xD7 slash_xD8 slash_xD9 slash_xDA slash_xDB
      slash_xDC slash_xDD slash_xDE slash_xDF slash_xE0 slash_xE1
      slash_xE2 slash_xE3 slash_xE4 slash_xE5 slash_xE6 slash_xE7
      slash_xE8 slash_xE9 slash_xEA slash_xEB slash_xEC slash_xED
      slash_xEE slash_xEF slash_xF0 slash_xF1 slash_xF2 slash_xF3
      slash_xF4 slash_xF5 slash_xF6 slash_xF7 slash_xF8 slash_xF9
      slash_xFA slash_xFB slash_xFC slash_xFD slash_xFE slash_xFF NUL_def
      SOH_def SYX_def ETX_def EOT_def ENQ_def ACK_def BEL_def BS_def
      HT_def LF_def VT_def FF_def CR_def SO_def SI_def DLE_def DC1_def
      DC2_def DC3_def DC4_def NAK_def SYN_def ETB_def CAN_def EM_def
      SUB_def ESC_def FS_def GS_def RS_def US_def SP_def DEL_def NL_def
      NP_def slash_n slash_t slash_v slash_b slash_r slash_f slash_a
      slash_quest
by (auto)

ML "Header.record \"StringT4\""

theorem StringT5 :
"ALL (x :: Char partial).
 ALL (y :: Char partial).
 ALL (z :: Char partial).
 x <_4 y & y <_4 z -->
 ~
 X_Cons x (X_Cons z (makePartial Nil')) <_4
 X_Cons x (X_Cons y (makePartial Nil'))"
using X1_def_Nat X2_def_Nat X3_def_Nat X4_def_Nat X5_def_Nat
      X6_def_Nat X7_def_Nat X8_def_Nat X9_def_Nat decimal_def Pos_def
      X1_as_Pos_def slash_000 slash_001 slash_002 slash_003 slash_004
      slash_005 slash_006 slash_007 slash_008 slash_009 slash_010
      slash_011 slash_012 slash_013 slash_014 slash_015 slash_016
      slash_017 slash_018 slash_019 slash_020 slash_021 slash_022
      slash_023 slash_024 slash_025 slash_026 slash_027 slash_028
      slash_029 slash_030 slash_031 slash_032 slash_033 slash_034
      slash_035 slash_036 slash_037 slash_038 slash_039 slash_040
      slash_041 slash_042 slash_043 slash_044 slash_045 slash_046
      slash_047 slash_048 slash_049 slash_050 slash_051 slash_052
      slash_053 slash_054 slash_055 slash_056 slash_057 slash_058
      slash_059 slash_060 slash_061 slash_062 slash_063 slash_064
      slash_065 slash_066 slash_067 slash_068 slash_069 slash_070
      slash_071 slash_072 slash_073 slash_074 slash_075 slash_076
      slash_077 slash_078 slash_079 slash_080 slash_081 slash_082
      slash_083 slash_084 slash_085 slash_086 slash_087 slash_088
      slash_089 slash_090 slash_091 slash_092 slash_093 slash_094
      slash_095 slash_096 slash_097 slash_098 slash_099 slash_100
      slash_101 slash_102 slash_103 slash_104 slash_105 slash_106
      slash_107 slash_108 slash_109 slash_110 slash_111 slash_112
      slash_113 slash_114 slash_115 slash_116 slash_117 slash_118
      slash_119 slash_120 slash_121 slash_122 slash_123 slash_124
      slash_125 slash_126 slash_127 slash_128 slash_129 slash_130
      slash_131 slash_132 slash_133 slash_134 slash_135 slash_136
      slash_137 slash_138 slash_139 slash_140 slash_141 slash_142
      slash_143 slash_144 slash_145 slash_146 slash_147 slash_148
      slash_149 slash_150 slash_151 slash_152 slash_153 slash_154
      slash_155 slash_156 slash_157 slash_158 slash_159 slash_160
      slash_161 slash_162 slash_163 slash_164 slash_165 slash_166
      slash_167 slash_168 slash_169 slash_170 slash_171 slash_172
      slash_173 slash_174 slash_175 slash_176 slash_177 slash_178
      slash_179 slash_180 slash_181 slash_182 slash_183 slash_184
      slash_185 slash_186 slash_187 slash_188 slash_189 slash_190
      slash_191 slash_192 slash_193 slash_194 slash_195 slash_196
      slash_197 slash_198 slash_199 slash_200 slash_201 slash_202
      slash_203 slash_204 slash_205 slash_206 slash_207 slash_208
      slash_209 slash_210 slash_211 slash_212 slash_213 slash_214
      slash_215 slash_216 slash_217 slash_218 slash_219 slash_220
      slash_221 slash_222 slash_223 slash_224 slash_225 slash_226
      slash_227 slash_228 slash_229 slash_230 slash_231 slash_232
      slash_233 slash_234 slash_235 slash_236 slash_237 slash_238
      slash_239 slash_240 slash_241 slash_242 slash_243 slash_244
      slash_245 slash_246 slash_247 slash_248 slash_249 slash_250
      slash_251 slash_252 slash_253 slash_254 slash_255 printable_32
      printable_33 printable_34 printable_35 printable_36 printable_37
      printable_38 printable_39 printable_40 printable_41 printable_42
      printable_43 printable_44 printable_45 printable_46 printable_47
      printable_48 printable_49 printable_50 printable_51 printable_52
      printable_53 printable_54 printable_55 printable_56 printable_57
      printable_58 printable_59 printable_60 printable_61 printable_62
      printable_63 printable_64 printable_65 printable_66 printable_67
      printable_68 printable_69 printable_70 printable_71 printable_72
      printable_73 printable_74 printable_75 printable_76 printable_77
      printable_78 printable_79 printable_80 printable_81 printable_82
      printable_83 printable_84 printable_85 printable_86 printable_87
      printable_88 printable_89 printable_90 printable_91 printable_92
      printable_93 printable_94 printable_95 printable_96 printable_97
      printable_98 printable_99 printable_100 printable_101 printable_102
      printable_103 printable_104 printable_105 printable_106
      printable_107 printable_108 printable_109 printable_110
      printable_111 printable_112 printable_113 printable_114
      printable_115 printable_116 printable_117 printable_118
      printable_119 printable_120 printable_121 printable_122
      printable_123 printable_124 printable_125 printable_126
      printable_160 printable_161 printable_162 printable_163
      printable_164 printable_165 printable_166 printable_167
      printable_168 printable_169 printable_170 printable_171
      printable_172 printable_173 printable_174 printable_175
      printable_176 printable_177 printable_178 printable_179
      printable_180 printable_181 printable_182 printable_183
      printable_184 printable_185 printable_186 printable_187
      printable_188 printable_189 printable_190 printable_191
      printable_192 printable_193 printable_194 printable_195
      printable_196 printable_197 printable_198 printable_199
      printable_200 printable_201 printable_202 printable_203
      printable_204 printable_205 printable_206 printable_207
      printable_208 printable_209 printable_210 printable_211
      printable_212 printable_213 printable_214 printable_215
      printable_216 printable_217 printable_218 printable_219
      printable_220 printable_221 printable_222 printable_223
      printable_224 printable_225 printable_226 printable_227
      printable_228 printable_229 printable_230 printable_231
      printable_232 printable_233 printable_234 printable_235
      printable_236 printable_237 printable_238 printable_239
      printable_240 printable_241 printable_242 printable_243
      printable_244 printable_245 printable_246 printable_247
      printable_248 printable_249 printable_250 printable_251
      printable_252 printable_253 printable_254 printable_255
      isLetter_def isDigit_def isPrintable_def slash_o000 slash_o001
      slash_o002 slash_o003 slash_o004 slash_o005 slash_o006 slash_o007
      slash_o010 slash_o011 slash_o012 slash_o013 slash_o014 slash_o015
      slash_o016 slash_o017 slash_o020 slash_o021 slash_o022 slash_o023
      slash_o024 slash_o025 slash_o026 slash_o027 slash_o030 slash_o031
      slash_o032 slash_o033 slash_o034 slash_o035 slash_o036 slash_o037
      slash_o040 slash_o041 slash_o042 slash_o043 slash_o044 slash_o045
      slash_o046 slash_o047 slash_o050 slash_o051 slash_o052 slash_o053
      slash_o054 slash_o055 slash_o056 slash_o057 slash_o060 slash_o061
      slash_o062 slash_o063 slash_o064 slash_o065 slash_o066 slash_o067
      slash_o070 slash_o071 slash_o072 slash_o073 slash_o074 slash_o075
      slash_o076 slash_o077 slash_o100 slash_o101 slash_o102 slash_o103
      slash_o104 slash_o105 slash_o106 slash_o107 slash_o110 slash_o111
      slash_o112 slash_o113 slash_o114 slash_o115 slash_o116 slash_o117
      slash_o120 slash_o121 slash_o122 slash_o123 slash_o124 slash_o125
      slash_o126 slash_o127 slash_o130 slash_o131 slash_o132 slash_o133
      slash_o134 slash_o135 slash_o136 slash_o137 slash_o140 slash_o141
      slash_o142 slash_o143 slash_o144 slash_o145 slash_o146 slash_o147
      slash_o150 slash_o151 slash_o152 slash_o153 slash_o154 slash_o155
      slash_o156 slash_o157 slash_o160 slash_o161 slash_o162 slash_o163
      slash_o164 slash_o165 slash_o166 slash_o167 slash_o170 slash_o171
      slash_o172 slash_o173 slash_o174 slash_o175 slash_o176 slash_o177
      slash_o200 slash_o201 slash_o202 slash_o203 slash_o204 slash_o205
      slash_o206 slash_o207 slash_o210 slash_o211 slash_o212 slash_o213
      slash_o214 slash_o215 slash_o216 slash_o217 slash_o220 slash_o221
      slash_o222 slash_o223 slash_o224 slash_o225 slash_o226 slash_o227
      slash_o230 slash_o231 slash_o232 slash_o233 slash_o234 slash_o235
      slash_o236 slash_o237 slash_o240 slash_o241 slash_o242 slash_o243
      slash_o244 slash_o245 slash_o246 slash_o247 slash_o250 slash_o251
      slash_o252 slash_o253 slash_o254 slash_o255 slash_o256 slash_o257
      slash_o260 slash_o261 slash_o262 slash_o263 slash_o264 slash_o265
      slash_o266 slash_o267 slash_o270 slash_o271 slash_o272 slash_o273
      slash_o274 slash_o275 slash_o276 slash_o277 slash_o300 slash_o301
      slash_o302 slash_o303 slash_o304 slash_o305 slash_o306 slash_o307
      slash_o310 slash_o311 slash_o312 slash_o313 slash_o314 slash_o315
      slash_o316 slash_o317 slash_o320 slash_o321 slash_o322 slash_o323
      slash_o324 slash_o325 slash_o326 slash_o327 slash_o330 slash_o331
      slash_o332 slash_o333 slash_o334 slash_o335 slash_o336 slash_o337
      slash_o340 slash_o341 slash_o342 slash_o343 slash_o344 slash_o345
      slash_o346 slash_o347 slash_o350 slash_o351 slash_o352 slash_o353
      slash_o354 slash_o355 slash_o356 slash_o357 slash_o360 slash_o361
      slash_o362 slash_o363 slash_o364 slash_o365 slash_o366 slash_o367
      slash_o370 slash_o371 slash_o372 slash_o373 slash_o374 slash_o375
      slash_o376 slash_o377 slash_x00 slash_x01 slash_x02 slash_x03
      slash_x04 slash_x05 slash_x06 slash_x07 slash_x08 slash_x09
      slash_x0A slash_x0B slash_x0C slash_x0D slash_x0E slash_x0F
      slash_x10 slash_x11 slash_x12 slash_x13 slash_x14 slash_x15
      slash_x16 slash_x17 slash_x18 slash_x19 slash_x1A slash_x1B
      slash_x1C slash_x1D slash_x1E slash_x1F slash_x20 slash_x21
      slash_x22 slash_x23 slash_x24 slash_x25 slash_x26 slash_x27
      slash_x28 slash_x29 slash_x2A slash_x2B slash_x2C slash_x2D
      slash_x2E slash_x2F slash_x30 slash_x31 slash_x32 slash_x33
      slash_x34 slash_x35 slash_x36 slash_x37 slash_x38 slash_x39
      slash_x3A slash_x3B slash_x3C slash_x3D slash_x3E slash_x3F
      slash_x40 slash_x41 slash_x42 slash_x43 slash_x44 slash_x45
      slash_x46 slash_x47 slash_x48 slash_x49 slash_x4A slash_x4B
      slash_x4C slash_x4D slash_x4E slash_x4F slash_x50 slash_x51
      slash_x52 slash_x53 slash_x54 slash_x55 slash_x56 slash_x57
      slash_x58 slash_x59 slash_x5A slash_x5B slash_x5C slash_x5D
      slash_x5E slash_x5F slash_x60 slash_x61 slash_x62 slash_x63
      slash_x64 slash_x65 slash_x66 slash_x67 slash_x68 slash_x69
      slash_x6A slash_x6B slash_x6C slash_x6D slash_x6E slash_x6F
      slash_x70 slash_x71 slash_x72 slash_x73 slash_x74 slash_x75
      slash_x76 slash_x77 slash_x78 slash_x79 slash_x7A slash_x7B
      slash_x7C slash_x7D slash_x7E slash_x7F slash_x80 slash_x81
      slash_x82 slash_x83 slash_x84 slash_x85 slash_x86 slash_x87
      slash_x88 slash_x89 slash_x8A slash_x8B slash_x8C slash_x8D
      slash_x8E slash_x8F slash_x90 slash_x91 slash_x92 slash_x93
      slash_x94 slash_x95 slash_x96 slash_x97 slash_x98 slash_x99
      slash_x9A slash_x9B slash_x9C slash_x9D slash_x9E slash_x9F
      slash_xA0 slash_xA1 slash_xA2 slash_xA3 slash_xA4 slash_xA5
      slash_xA6 slash_xA7 slash_xA8 slash_xA9 slash_xAA slash_xAB
      slash_xAC slash_xAD slash_xAE slash_xAF slash_xB0 slash_xB1
      slash_xB2 slash_xB3 slash_xB4 slash_xB5 slash_xB6 slash_xB7
      slash_xB8 slash_xB9 slash_xBA slash_xBB slash_xBC slash_xBD
      slash_xBE slash_xBF slash_xC0 slash_xC1 slash_xC2 slash_xC3
      slash_xC4 slash_xC5 slash_xC6 slash_xC7 slash_xC8 slash_xC9
      slash_xCA slash_xCB slash_xCC slash_xCD slash_xCE slash_xCF
      slash_xD0 slash_xD1 slash_xD2 slash_xD3 slash_xD4 slash_xD5
      slash_xD6 slash_xD7 slash_xD8 slash_xD9 slash_xDA slash_xDB
      slash_xDC slash_xDD slash_xDE slash_xDF slash_xE0 slash_xE1
      slash_xE2 slash_xE3 slash_xE4 slash_xE5 slash_xE6 slash_xE7
      slash_xE8 slash_xE9 slash_xEA slash_xEB slash_xEC slash_xED
      slash_xEE slash_xEF slash_xF0 slash_xF1 slash_xF2 slash_xF3
      slash_xF4 slash_xF5 slash_xF6 slash_xF7 slash_xF8 slash_xF9
      slash_xFA slash_xFB slash_xFC slash_xFD slash_xFE slash_xFF NUL_def
      SOH_def SYX_def ETX_def EOT_def ENQ_def ACK_def BEL_def BS_def
      HT_def LF_def VT_def FF_def CR_def SO_def SI_def DLE_def DC1_def
      DC2_def DC3_def DC4_def NAK_def SYN_def ETB_def CAN_def EM_def
      SUB_def ESC_def FS_def GS_def RS_def US_def SP_def DEL_def NL_def
      NP_def slash_n slash_t slash_v slash_b slash_r slash_f slash_a
      slash_quest
by (auto)

ML "Header.record \"StringT5\""

end
