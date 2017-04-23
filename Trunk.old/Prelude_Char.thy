theory Prelude_Char
imports "$HETS_LIB/Isabelle/MainHCPairs"
uses "$HETS_LIB/Isabelle/prelude"
begin

ML "Header.initialize
    [\"ga_selector_pre\", \"ga_injective_suc\", \"ga_disjoint_0_suc\",
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
     \"ga_left_comm_max\", \"leq_def1_Nat\", \"leq_def2_Nat\",
     \"leq_def3_Nat\", \"geq_def_Nat\", \"less_def_Nat\",
     \"greater_def_Nat\", \"even_0_Nat\", \"even_suc_Nat\",
     \"odd_def_Nat\", \"factorial_0\", \"factorial_suc\", \"add_0_Nat\",
     \"add_suc_Nat\", \"mult_0_Nat\", \"mult_suc_Nat\", \"power_0_Nat\",
     \"power_suc_Nat\", \"min_def_Nat\", \"max_def_Nat\",
     \"subTotal_def1_Nat\", \"subTotal_def2_Nat\", \"sub_dom_Nat\",
     \"sub_def_Nat\", \"divide_dom_Nat\", \"divide_0_Nat\",
     \"divide_Pos_Nat\", \"div_dom_Nat\", \"div_Nat\", \"mod_dom_Nat\",
     \"mod_Nat\", \"distr1_Nat\", \"distr2_Nat\", \"min_0\",
     \"div_mod_Nat\", \"power_Nat\", \"NotFalse\", \"NotTrue\",
     \"AndFalse\", \"AndTrue\", \"AndSym\", \"OrDef\", \"OtherwiseDef\",
     \"NotFalse1\", \"NotTrue1\", \"notNot1\", \"notNot2\",
     \"EqualTDef\", \"EqualSymDef\", \"EqualReflex\", \"EqualTransT\",
     \"DiffDef\", \"DiffSymDef\", \"DiffTDef\", \"DiffFDef\", \"TE1\",
     \"TE2\", \"TE3\", \"TE4\", \"IBE1\", \"IBE2\", \"IBE3\", \"IBE4\",
     \"IBE5\", \"IBE6\", \"IBE7\", \"IBE8\", \"IUE1\", \"IUE2\",
     \"IOE01\", \"IOE02\", \"IOE03\", \"IOE04\", \"IOE05\", \"IOE06\",
     \"IOE07\", \"IOE08\", \"IOE09\", \"LeIrreflexivity\",
     \"LeTAsymmetry\", \"LeTTransitive\", \"LeTTotal\", \"GeDef\",
     \"GeIrreflexivity\", \"GeTAsymmetry\", \"GeTTransitive\",
     \"GeTTotal\", \"LeqDef\", \"LeqReflexivity\", \"LeqTTransitive\",
     \"LeqTTotal\", \"GeqDef\", \"GeqReflexivity\", \"GeqTTransitive\",
     \"GeqTTotal\", \"EqTSOrdRel\", \"EqFSOrdRel\", \"EqTOrdRel\",
     \"EqFOrdRel\", \"EqTOrdTSubstE\", \"EqTOrdFSubstE\",
     \"EqTOrdTSubstD\", \"EqTOrdFSubstD\", \"LeTGeTRel\", \"LeFGeFRel\",
     \"LeqTGetTRel\", \"LeqFGetFRel\", \"GeTLeTRel\", \"GeFLeFRel\",
     \"GeqTLeqTRel\", \"GeqFLeqFRel\", \"LeTGeFEqFRel\",
     \"LeFGeTEqTRel\", \"LeqTGeFRel\", \"LeqFGeTRel\", \"GeTLeFEqFRel\",
     \"GeFLeTEqTRel\", \"GeqTLeFRel\", \"GeqFLeTRel\",
     \"LeqTLeTEqTRel\", \"LeqFLeFEqFRel\", \"GeqTGeTEqTRel\",
     \"GeqFGeFEqFRel\", \"LeTGeqFRel\", \"GeTLeqFRel\", \"LeLeqDiff\",
     \"CmpLTDef\", \"CmpEQDef\", \"CmpGTDef\", \"MaxYDef\", \"MaxXDef\",
     \"MinXDef\", \"MinYDef\", \"MaxSym\", \"MinSym\", \"TO1\", \"TO2\",
     \"TO3\", \"TO4\", \"TO5\", \"TO6\", \"TO7\", \"IOO13\", \"IOO14\",
     \"IOO15\", \"IOO16\", \"IOO17\", \"IOO18\", \"IOO19\", \"IOO20\",
     \"IOO21\", \"IOO22\", \"IOO23\", \"IOO24\", \"IOO25\", \"IOO26\",
     \"IOO27\", \"IOO28\", \"IOO29\", \"IOO30\", \"IOO31\", \"IOO32\",
     \"IOO33\", \"IBO5\", \"IBO6\", \"IBO7\", \"IBO8\", \"IBO9\",
     \"IBO10\", \"IBO11\", \"IBO12\", \"IUO01\", \"IUO02\", \"IUO03\",
     \"IUO04\", \"IUO05\", \"IUO06\", \"IUO07\", \"ga_select_ord\",
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
     \"isLetter_def\", \"isDigit_def\", \"isPrintable_def\",
     \"NUL_def\", \"SOH_def\", \"SYX_def\", \"ETX_def\", \"EOT_def\",
     \"ENQ_def\", \"ACK_def\", \"BEL_def\", \"BS_def\", \"HT_def\",
     \"LF_def\", \"VT_def\", \"FF_def\", \"CR_def\", \"SO_def\",
     \"SI_def\", \"DLE_def\", \"DC1_def\", \"DC2_def\", \"DC3_def\",
     \"DC4_def\", \"NAK_def\", \"SYN_def\", \"ETB_def\", \"CAN_def\",
     \"EM_def\", \"SUB_def\", \"ESC_def\", \"FS_def\", \"GS_def\",
     \"RS_def\", \"US_def\", \"SP_def\", \"DEL_def\", \"NL_def\",
     \"NP_def\", \"slash_n\", \"slash_t\", \"slash_v\", \"slash_b\",
     \"slash_r\", \"slash_f\", \"slash_a\", \"slash_quest\", \"ICE01\",
     \"ICE02\", \"ICO01\", \"ICO02\", \"ICO03\", \"ICO04\", \"ICO08\",
     \"ICO10\", \"ICO05\", \"ICO06\", \"ICO07\", \"ICO09\", \"ICO11\"]"

typedecl Char
typedecl Unit

datatype Nat = X0 ("0''") | X_suc "Nat" ("suc/'(_')" [3] 999)
datatype Bool = X_False ("False''") | X_True ("True''")
datatype Ordering = EQ | GT | LT

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
Not__X :: "Bool => Bool" ("(Not''/ _)" [56] 56)
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
X'XAmp' :: "Char" ("''&''")
X'XAt' :: "Char" ("''@''")
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
X'XBslashr' :: "Char" ("''\\r''")
X'XBslasht' :: "Char" ("''\\t''")
X'XBslashv' :: "Char" ("''\\v''")
X'XCBr' :: "Char" ("''')''")
X'XCSqBr' :: "Char" ("'']''")
X'XCaret' :: "Char" ("''^''")
X'XColon' :: "Char" ("'':''")
X'XComma' :: "Char" ("'',''")
X'XDollar' :: "Char" ("''$''")
X'XEq' :: "Char" ("''=''")
X'XExclam' :: "Char" ("''!''")
X'XGrave' :: "Char" ("''`''")
X'XGt' :: "Char" ("''>''")
X'XHash' :: "Char" ("''#''")
X'XLBrace' :: "Char" ("''{''")
X'XLt' :: "Char" ("''<''")
X'XMinus' :: "Char" ("''-''")
X'XOBr' :: "Char" ("'''(''")
X'XOSqBr' :: "Char" ("''[''")
X'XPercent' :: "Char" ("''%''")
X'XPeriod' :: "Char" ("''.''")
X'XPlus' :: "Char" ("''+''")
X'XQuest' :: "Char" ("''?''")
X'XRBrace' :: "Char" ("''}''")
X'XSemi' :: "Char" ("'';''")
X'XSlash' :: "Char" ("'''/''")
X'XSlash_32' :: "Char" ("'' ''")
X'XTilde' :: "Char" ("''~''")
X'XVBar' :: "Char" ("''|''")
X'XX' :: "Char" ("''X''")
X'Xx' :: "Char" ("''*''")
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
X1 :: "Nat" ("1''")
X2 :: "Nat" ("2''")
X3 :: "Nat" ("3''")
X4 :: "Nat" ("4''")
X5 :: "Nat" ("5''")
X6 :: "Nat" ("6''")
X7 :: "Nat" ("7''")
X8 :: "Nat" ("8''")
X9 :: "Nat" ("9''")
X__XAmpXAmp__X :: "Bool => Bool => Bool" ("(_/ &&/ _)" [54,54] 52)
X__XAtXAt__X :: "Nat => Nat => Nat" ("(_/ @@/ _)" [54,54] 52)
X__XCaret__X :: "Nat => Nat => Nat" ("(_/ ^''/ _)" [54,54] 52)
X__XEqXEq__X :: "'a => 'a => Bool" ("(_/ ==''/ _)" [54,54] 52)
X__XExclam :: "Nat => Nat" ("(_/ !'')" [58] 58)
X__XGtXEq__XX1 :: "Nat => Nat => bool" ("(_/ >=''/ _)" [44,44] 42)
X__XGtXEq__XX2 :: "'a => 'a => Bool" ("(_/ >=''''/ _)" [54,54] 52)
X__XGt__XX1 :: "Nat => Nat => bool" ("(_/ >''/ _)" [44,44] 42)
X__XGt__XX2 :: "'a => 'a => Bool" ("(_/ >''''/ _)" [54,54] 52)
X__XLtXEq__XX1 :: "Nat => Nat => bool" ("(_/ <=''/ _)" [44,44] 42)
X__XLtXEq__XX2 :: "'a => 'a => Bool" ("(_/ <=''''/ _)" [54,54] 52)
X__XLt__XX1 :: "Nat => Nat => bool" ("(_/ <''/ _)" [44,44] 42)
X__XLt__XX2 :: "'a => 'a => Bool" ("(_/ <''''/ _)" [54,54] 52)
X__XMinusXExclam__X :: "Nat => Nat => Nat" ("(_/ -!/ _)" [54,54] 52)
X__XMinusXQuest__X :: "Nat => Nat => Nat partial" ("(_/ -?/ _)" [54,54] 52)
X__XPlus__X :: "Nat => Nat => Nat" ("(_/ +''/ _)" [54,54] 52)
X__XSlashXEq__X :: "'a => 'a => Bool" ("(_/ '/=/ _)" [54,54] 52)
X__XSlashXQuest__X :: "Nat => Nat => Nat partial" ("(_/ '/?/ _)" [54,54] 52)
X__XVBarXVBar__X :: "Bool => Bool => Bool" ("(_/ ||/ _)" [54,54] 52)
X__Xx__X :: "Nat => Nat => Nat" ("(_/ *''/ _)" [54,54] 52)
X__div__X :: "Nat => Nat => Nat partial" ("(_/ div''/ _)" [54,54] 52)
X__mod__X :: "Nat => Nat => Nat partial" ("(_/ mod''/ _)" [54,54] 52)
X_chr :: "Nat => Char partial" ("chr/'(_')" [3] 999)
X_even :: "Nat => bool" ("even''/'(_')" [3] 999)
X_isDigit :: "Char => bool" ("isDigit/'(_')" [3] 999)
X_isLetter :: "Char => bool" ("isLetter/'(_')" [3] 999)
X_isPrintable :: "Char => bool" ("isPrintable/'(_')" [3] 999)
X_maxX1 :: "Nat => Nat => Nat" ("max''/'(_,/ _')" [3,3] 999)
X_maxX2 :: "'a => 'a => 'a"
X_minX1 :: "Nat => Nat => Nat" ("min''/'(_,/ _')" [3,3] 999)
X_minX2 :: "'a => 'a => 'a"
X_odd :: "Nat => bool" ("odd''/'(_')" [3] 999)
X_ord :: "Char => Nat" ("ord''/'(_')" [3] 999)
X_pre :: "Nat => Nat partial" ("pre/'(_')" [3] 999)
compare :: "'a => 'a => Ordering"
otherwiseH :: "Bool"

axioms
ga_selector_pre [rule_format] :
"ALL XX1. pre(suc(XX1)) = makePartial XX1"

ga_injective_suc [rule_format] :
"ALL XX1. ALL Y1. suc(XX1) = suc(Y1) = (XX1 = Y1)"

ga_disjoint_0_suc [rule_format] : "ALL Y1. ~ 0' = suc(Y1)"

ga_selector_undef_pre_0 [rule_format] : "~ defOp (pre(0'))"

X1_def_Nat [rule_format] : "1' = suc(0')"

X2_def_Nat [rule_format] : "2' = suc(1')"

X3_def_Nat [rule_format] : "3' = suc(2')"

X4_def_Nat [rule_format] : "4' = suc(3')"

X5_def_Nat [rule_format] : "5' = suc(4')"

X6_def_Nat [rule_format] : "6' = suc(5')"

X7_def_Nat [rule_format] : "7' = suc(6')"

X8_def_Nat [rule_format] : "8' = suc(7')"

X9_def_Nat [rule_format] : "9' = suc(8')"

decimal_def [rule_format] :
"ALL m. ALL X_n. m @@ X_n = (m *' suc(9')) +' X_n"

ga_comm___XPlus__ [rule_format] : "ALL x. ALL y. x +' y = y +' x"

ga_assoc___XPlus__ [rule_format] :
"ALL x. ALL y. ALL z. (x +' y) +' z = x +' (y +' z)"

ga_right_unit___XPlus__ [rule_format] : "ALL x. x +' 0' = x"

ga_left_unit___XPlus__ [rule_format] : "ALL x. 0' +' x = x"

ga_left_comm___XPlus__ [rule_format] :
"ALL x. ALL y. ALL z. x +' (y +' z) = y +' (x +' z)"

ga_comm___Xx__ [rule_format] : "ALL x. ALL y. x *' y = y *' x"

ga_assoc___Xx__ [rule_format] :
"ALL x. ALL y. ALL z. (x *' y) *' z = x *' (y *' z)"

ga_right_unit___Xx__ [rule_format] : "ALL x. x *' 1' = x"

ga_left_unit___Xx__ [rule_format] : "ALL x. 1' *' x = x"

ga_left_comm___Xx__ [rule_format] :
"ALL x. ALL y. ALL z. x *' (y *' z) = y *' (x *' z)"

ga_comm_min [rule_format] : "ALL x. ALL y. min'(x, y) = min'(y, x)"

ga_assoc_min [rule_format] :
"ALL x. ALL y. ALL z. min'(min'(x, y), z) = min'(x, min'(y, z))"

ga_left_comm_min [rule_format] :
"ALL x. ALL y. ALL z. min'(x, min'(y, z)) = min'(y, min'(x, z))"

ga_comm_max [rule_format] : "ALL x. ALL y. max'(x, y) = max'(y, x)"

ga_assoc_max [rule_format] :
"ALL x. ALL y. ALL z. max'(max'(x, y), z) = max'(x, max'(y, z))"

ga_right_unit_max [rule_format] : "ALL x. max'(x, 0') = x"

ga_left_unit_max [rule_format] : "ALL x. max'(0', x) = x"

ga_left_comm_max [rule_format] :
"ALL x. ALL y. ALL z. max'(x, max'(y, z)) = max'(y, max'(x, z))"

leq_def1_Nat [rule_format] : "ALL X_n. 0' <=' X_n"

leq_def2_Nat [rule_format] : "ALL X_n. ~ suc(X_n) <=' 0'"

leq_def3_Nat [rule_format] :
"ALL m. ALL X_n. (suc(m) <=' suc(X_n)) = (m <=' X_n)"

geq_def_Nat [rule_format] :
"ALL m. ALL X_n. (m >=' X_n) = (X_n <=' m)"

less_def_Nat [rule_format] :
"ALL m. ALL X_n. (m <' X_n) = (m <=' X_n & ~ m = X_n)"

greater_def_Nat [rule_format] :
"ALL m. ALL X_n. (m >' X_n) = (X_n <' m)"

even_0_Nat [rule_format] : "even'(0')"

even_suc_Nat [rule_format] : "ALL m. even'(suc(m)) = odd'(m)"

odd_def_Nat [rule_format] : "ALL m. odd'(m) = (~ even'(m))"

factorial_0 [rule_format] : "0' !' = 1'"

factorial_suc [rule_format] :
"ALL X_n. suc(X_n) !' = suc(X_n) *' X_n !'"

add_0_Nat [rule_format] : "ALL m. 0' +' m = m"

add_suc_Nat [rule_format] :
"ALL m. ALL X_n. suc(X_n) +' m = suc(X_n +' m)"

mult_0_Nat [rule_format] : "ALL m. 0' *' m = 0'"

mult_suc_Nat [rule_format] :
"ALL m. ALL X_n. suc(X_n) *' m = (X_n *' m) +' m"

power_0_Nat [rule_format] : "ALL m. m ^' 0' = 1'"

power_suc_Nat [rule_format] :
"ALL m. ALL X_n. m ^' suc(X_n) = m *' (m ^' X_n)"

min_def_Nat [rule_format] :
"ALL m. ALL X_n. min'(m, X_n) = (if m <=' X_n then m else X_n)"

max_def_Nat [rule_format] :
"ALL m. ALL X_n. max'(m, X_n) = (if m <=' X_n then X_n else m)"

subTotal_def1_Nat [rule_format] :
"ALL m. ALL X_n. m >' X_n --> X_n -! m = 0'"

subTotal_def2_Nat [rule_format] :
"ALL m. ALL X_n. m <=' X_n --> makePartial (X_n -! m) = X_n -? m"

sub_dom_Nat [rule_format] :
"ALL m. ALL X_n. defOp (m -? X_n) = (m >=' X_n)"

sub_def_Nat [rule_format] :
"ALL m. ALL X_n. ALL r. m -? X_n = makePartial r = (m = r +' X_n)"

divide_dom_Nat [rule_format] :
"ALL m.
 ALL X_n.
 defOp (m /? X_n) = (~ X_n = 0' & m mod' X_n = makePartial 0')"

divide_0_Nat [rule_format] : "ALL m. ~ defOp (m /? 0')"

divide_Pos_Nat [rule_format] :
"ALL m.
 ALL X_n.
 ALL r. X_n >' 0' --> m /? X_n = makePartial r = (m = r *' X_n)"

div_dom_Nat [rule_format] :
"ALL m. ALL X_n. defOp (m div' X_n) = (~ X_n = 0')"

div_Nat [rule_format] :
"ALL m.
 ALL X_n.
 ALL r.
 m div' X_n = makePartial r =
 (EX s. m = (X_n *' r) +' s & s <' X_n)"

mod_dom_Nat [rule_format] :
"ALL m. ALL X_n. defOp (m mod' X_n) = (~ X_n = 0')"

mod_Nat [rule_format] :
"ALL m.
 ALL X_n.
 ALL s.
 m mod' X_n = makePartial s =
 (EX r. m = (X_n *' r) +' s & s <' X_n)"

distr1_Nat [rule_format] :
"ALL r. ALL s. ALL t. (r +' s) *' t = (r *' t) +' (s *' t)"

distr2_Nat [rule_format] :
"ALL r. ALL s. ALL t. t *' (r +' s) = (t *' r) +' (t *' s)"

min_0 [rule_format] : "ALL m. min'(m, 0') = 0'"

div_mod_Nat [rule_format] :
"ALL m.
 ALL X_n.
 ~ X_n = 0' -->
 makePartial m =
 (let (Xb5, Xc0) =
      let (Xb4, Xc3) = m div' X_n
      in if Xb4 then makePartial (Xc3 *' X_n) else noneOp
  in if Xb5
        then let (Xb2, Xc1) = m mod' X_n
             in if Xb2 then makePartial (Xc0 +' Xc1) else noneOp
        else noneOp)"

power_Nat [rule_format] :
"ALL m. ALL r. ALL s. m ^' (r +' s) = (m ^' r) *' (m ^' s)"

NotFalse [rule_format] : "Not' False' = True'"

NotTrue [rule_format] : "Not' True' = False'"

AndFalse [rule_format] : "ALL x. False' && x = False'"

AndTrue [rule_format] : "ALL x. True' && x = x"

AndSym [rule_format] : "ALL x. ALL y. x && y = y && x"

OrDef [rule_format] :
"ALL x. ALL y. x || y = Not' (Not' x && Not' y)"

OtherwiseDef [rule_format] : "otherwiseH = True'"

NotFalse1 [rule_format] : "ALL x. Not' x = True' = (x = False')"

NotTrue1 [rule_format] : "ALL x. Not' x = False' = (x = True')"

notNot1 [rule_format] : "ALL x. (~ x = True') = (Not' x = True')"

notNot2 [rule_format] : "ALL x. (~ x = False') = (Not' x = False')"

EqualTDef [rule_format] : "ALL x. ALL y. x = y --> x ==' y = True'"

EqualSymDef [rule_format] : "ALL x. ALL y. x ==' y = y ==' x"

EqualReflex [rule_format] : "ALL x. x ==' x = True'"

EqualTransT [rule_format] :
"ALL x.
 ALL y.
 ALL z. x ==' y = True' & y ==' z = True' --> x ==' z = True'"

DiffDef [rule_format] : "ALL x. ALL y. x /= y = Not' (x ==' y)"

DiffSymDef [rule_format] : "ALL x. ALL y. x /= y = y /= x"

DiffTDef [rule_format] :
"ALL x. ALL y. x /= y = True' = (Not' (x ==' y) = True')"

DiffFDef [rule_format] :
"ALL x. ALL y. x /= y = False' = (x ==' y = True')"

TE1 [rule_format] : "ALL x. ALL y. x ==' y = False' --> ~ x = y"

TE2 [rule_format] :
"ALL x. ALL y. Not' (x ==' y) = True' = (x ==' y = False')"

TE3 [rule_format] :
"ALL x. ALL y. Not' (x ==' y) = False' = (x ==' y = True')"

TE4 [rule_format] :
"ALL x. ALL y. (~ x ==' y = True') = (x ==' y = False')"

IBE1 [rule_format] : "True' ==' True' = True'"

IBE2 [rule_format] : "False' ==' False' = True'"

IBE3 [rule_format] : "False' ==' True' = False'"

IBE4 [rule_format] : "True' ==' False' = False'"

IBE5 [rule_format] : "True' /= False' = True'"

IBE6 [rule_format] : "False' /= True' = True'"

IBE7 [rule_format] : "Not' (True' ==' False') = True'"

IBE8 [rule_format] : "Not' Not' (True' ==' False') = False'"

IUE1 [rule_format] : "() ==' () = True'"

IUE2 [rule_format] : "() /= () = False'"

IOE01 [rule_format] : "LT ==' LT = True'"

IOE02 [rule_format] : "EQ ==' EQ = True'"

IOE03 [rule_format] : "GT ==' GT = True'"

IOE04 [rule_format] : "LT ==' EQ = False'"

IOE05 [rule_format] : "LT ==' GT = False'"

IOE06 [rule_format] : "EQ ==' GT = False'"

IOE07 [rule_format] : "LT /= EQ = True'"

IOE08 [rule_format] : "LT /= GT = True'"

IOE09 [rule_format] : "EQ /= GT = True'"

LeIrreflexivity [rule_format] :
"ALL x. ALL y. x ==' y = True' --> x <'' y = False'"

LeTAsymmetry [rule_format] :
"ALL x. ALL y. x <'' y = True' --> y <'' x = False'"

LeTTransitive [rule_format] :
"ALL x.
 ALL y.
 ALL z. x <'' y = True' & y <'' z = True' --> x <'' z = True'"

LeTTotal [rule_format] :
"ALL x.
 ALL y. (x <'' y = True' | y <'' x = True') | x ==' y = True'"

GeDef [rule_format] : "ALL x. ALL y. x >'' y = y <'' x"

GeIrreflexivity [rule_format] :
"ALL x. ALL y. x ==' y = True' --> x >'' y = False'"

GeTAsymmetry [rule_format] :
"ALL x. ALL y. x >'' y = True' --> y >'' x = False'"

GeTTransitive [rule_format] :
"ALL x.
 ALL y. ALL z. (x >'' y) && (y >'' z) = True' --> x >'' z = True'"

GeTTotal [rule_format] :
"ALL x. ALL y. ((x >'' y) || (y >'' x)) || (x ==' y) = True'"

LeqDef [rule_format] :
"ALL x. ALL y. x <='' y = (x <'' y) || (x ==' y)"

LeqReflexivity [rule_format] : "ALL x. x <='' x = True'"

LeqTTransitive [rule_format] :
"ALL x.
 ALL y.
 ALL z. (x <='' y) && (y <='' z) = True' --> x <='' z = True'"

LeqTTotal [rule_format] :
"ALL x. ALL y. (x <='' y) && (y <='' x) = x ==' y"

GeqDef [rule_format] :
"ALL x. ALL y. x >='' y = (x >'' y) || (x ==' y)"

GeqReflexivity [rule_format] : "ALL x. x >='' x = True'"

GeqTTransitive [rule_format] :
"ALL x.
 ALL y.
 ALL z. (x >='' y) && (y >='' z) = True' --> x >='' z = True'"

GeqTTotal [rule_format] :
"ALL x. ALL y. (x >='' y) && (y >='' x) = x ==' y"

EqTSOrdRel [rule_format] :
"ALL x.
 ALL y. x ==' y = True' = (x <'' y = False' & x >'' y = False')"

EqFSOrdRel [rule_format] :
"ALL x.
 ALL y. x ==' y = False' = (x <'' y = True' | x >'' y = True')"

EqTOrdRel [rule_format] :
"ALL x.
 ALL y. x ==' y = True' = (x <='' y = True' & x >='' y = True')"

EqFOrdRel [rule_format] :
"ALL x.
 ALL y. x ==' y = False' = (x <='' y = True' | x >='' y = True')"

EqTOrdTSubstE [rule_format] :
"ALL x.
 ALL y.
 ALL z. x ==' y = True' & y <'' z = True' --> x <'' z = True'"

EqTOrdFSubstE [rule_format] :
"ALL x.
 ALL y.
 ALL z. x ==' y = True' & y <'' z = False' --> x <'' z = False'"

EqTOrdTSubstD [rule_format] :
"ALL x.
 ALL y.
 ALL z. x ==' y = True' & z <'' y = True' --> z <'' x = True'"

EqTOrdFSubstD [rule_format] :
"ALL x.
 ALL y.
 ALL z. x ==' y = True' & z <'' y = False' --> z <'' x = False'"

LeTGeTRel [rule_format] :
"ALL x. ALL y. x <'' y = True' = (y >'' x = True')"

LeFGeFRel [rule_format] :
"ALL x. ALL y. x <'' y = False' = (y >'' x = False')"

LeqTGetTRel [rule_format] :
"ALL x. ALL y. x <='' y = True' = (y >='' x = True')"

LeqFGetFRel [rule_format] :
"ALL x. ALL y. x <='' y = False' = (y >='' x = False')"

GeTLeTRel [rule_format] :
"ALL x. ALL y. x >'' y = True' = (y <'' x = True')"

GeFLeFRel [rule_format] :
"ALL x. ALL y. x >'' y = False' = (y <'' x = False')"

GeqTLeqTRel [rule_format] :
"ALL x. ALL y. x >='' y = True' = (y <='' x = True')"

GeqFLeqFRel [rule_format] :
"ALL x. ALL y. x >='' y = False' = (y <='' x = False')"

LeTGeFEqFRel [rule_format] :
"ALL x.
 ALL y. x <'' y = True' = (x >'' y = False' & x ==' y = False')"

LeFGeTEqTRel [rule_format] :
"ALL x.
 ALL y. x <'' y = False' = (x >'' y = True' | x ==' y = True')"

LeqTGeFRel [rule_format] :
"ALL x. ALL y. x <='' y = True' = (x >'' y = False')"

LeqFGeTRel [rule_format] :
"ALL x. ALL y. x <='' y = False' = (x >'' y = True')"

GeTLeFEqFRel [rule_format] :
"ALL x.
 ALL y. x >'' y = True' = (x <'' y = False' & x ==' y = False')"

GeFLeTEqTRel [rule_format] :
"ALL x.
 ALL y. x >'' y = False' = (x <'' y = True' | x ==' y = True')"

GeqTLeFRel [rule_format] :
"ALL x. ALL y. x >='' y = True' = (x <'' y = False')"

GeqFLeTRel [rule_format] :
"ALL x. ALL y. x >='' y = False' = (x <'' y = True')"

LeqTLeTEqTRel [rule_format] :
"ALL x.
 ALL y. x <='' y = True' = (x <'' y = True' | x ==' y = True')"

LeqFLeFEqFRel [rule_format] :
"ALL x.
 ALL y. x <='' y = False' = (x <'' y = False' & x ==' y = False')"

GeqTGeTEqTRel [rule_format] :
"ALL x.
 ALL y. x >='' y = True' = (x >'' y = True' | x ==' y = True')"

GeqFGeFEqFRel [rule_format] :
"ALL x.
 ALL y. x >='' y = False' = (x >'' y = False' & x ==' y = False')"

LeTGeqFRel [rule_format] :
"ALL x. ALL y. x <'' y = True' = (x >='' y = False')"

GeTLeqFRel [rule_format] :
"ALL x. ALL y. x >'' y = True' = (x <='' y = False')"

LeLeqDiff [rule_format] :
"ALL x. ALL y. x <'' y = (x <='' y) && (x /= y)"

CmpLTDef [rule_format] :
"ALL x. ALL y. compare x y ==' LT = x <'' y"

CmpEQDef [rule_format] :
"ALL x. ALL y. compare x y ==' EQ = x ==' y"

CmpGTDef [rule_format] :
"ALL x. ALL y. compare x y ==' GT = x >'' y"

MaxYDef [rule_format] :
"ALL x. ALL y. X_maxX2 x y ==' y = x <='' y"

MaxXDef [rule_format] :
"ALL x. ALL y. X_maxX2 x y ==' x = y <='' x"

MinXDef [rule_format] :
"ALL x. ALL y. X_minX2 x y ==' x = x <='' y"

MinYDef [rule_format] :
"ALL x. ALL y. X_minX2 x y ==' y = y <='' x"

MaxSym [rule_format] :
"ALL x. ALL y. X_maxX2 x y ==' y = X_maxX2 y x ==' y"

MinSym [rule_format] :
"ALL x. ALL y. X_minX2 x y ==' y = X_minX2 y x ==' y"

TO1 [rule_format] :
"ALL x.
 ALL y. (x ==' y = True' | x <'' y = True') = (x <='' y = True')"

TO2 [rule_format] :
"ALL x. ALL y. x ==' y = True' --> x <'' y = False'"

TO3 [rule_format] :
"ALL x.
 ALL y. Not' Not' (x <'' y) = True' | Not' (x <'' y) = True'"

TO4 [rule_format] :
"ALL x. ALL y. x <'' y = True' --> Not' (x ==' y) = True'"

TO5 [rule_format] :
"ALL w.
 ALL x.
 ALL y.
 ALL z.
 (x <'' y = True' & y <'' z = True') & z <'' w = True' -->
 x <'' w = True'"

TO6 [rule_format] :
"ALL x. ALL z. z <'' x = True' --> Not' (x <'' z) = True'"

TO7 [rule_format] :
"ALL x. ALL y. x <'' y = True' = (y >'' x = True')"

IOO13 [rule_format] : "LT <'' EQ = True'"

IOO14 [rule_format] : "EQ <'' GT = True'"

IOO15 [rule_format] : "LT <'' GT = True'"

IOO16 [rule_format] : "LT <='' EQ = True'"

IOO17 [rule_format] : "EQ <='' GT = True'"

IOO18 [rule_format] : "LT <='' GT = True'"

IOO19 [rule_format] : "EQ >='' LT = True'"

IOO20 [rule_format] : "GT >='' EQ = True'"

IOO21 [rule_format] : "GT >='' LT = True'"

IOO22 [rule_format] : "EQ >'' LT = True'"

IOO23 [rule_format] : "GT >'' EQ = True'"

IOO24 [rule_format] : "GT >'' LT = True'"

IOO25 [rule_format] : "X_maxX2 LT EQ ==' EQ = True'"

IOO26 [rule_format] : "X_maxX2 EQ GT ==' GT = True'"

IOO27 [rule_format] : "X_maxX2 LT GT ==' GT = True'"

IOO28 [rule_format] : "X_minX2 LT EQ ==' LT = True'"

IOO29 [rule_format] : "X_minX2 EQ GT ==' EQ = True'"

IOO30 [rule_format] : "X_minX2 LT GT ==' LT = True'"

IOO31 [rule_format] : "compare LT LT ==' EQ = True'"

IOO32 [rule_format] : "compare EQ EQ ==' EQ = True'"

IOO33 [rule_format] : "compare GT GT ==' EQ = True'"

IBO5 [rule_format] : "False' <'' True' = True'"

IBO6 [rule_format] : "False' >='' True' = False'"

IBO7 [rule_format] : "True' >='' False' = True'"

IBO8 [rule_format] : "True' <'' False' = False'"

IBO9 [rule_format] : "X_maxX2 False' True' ==' True' = True'"

IBO10 [rule_format] : "X_minX2 False' True' ==' False' = True'"

IBO11 [rule_format] : "compare True' True' ==' EQ = True'"

IBO12 [rule_format] : "compare False' False' ==' EQ = True'"

IUO01 [rule_format] : "() <='' () = True'"

IUO02 [rule_format] : "() <'' () = False'"

IUO03 [rule_format] : "() >='' () = True'"

IUO04 [rule_format] : "() >'' () = False'"

IUO05 [rule_format] : "X_maxX2 () () ==' () = True'"

IUO06 [rule_format] : "X_minX2 () () ==' () = True'"

IUO07 [rule_format] : "compare () () ==' EQ = True'"

ga_select_ord [rule_format] :
"ALL x_1_1.
 (let (Xb1, Xc0) = chr(x_1_1)
  in if Xb1 then makePartial (ord'(Xc0)) else noneOp) =
 makePartial x_1_1"

chr_dom [rule_format] :
"ALL X_n. defOp (chr(X_n)) = (X_n <=' 2' @@ (5' @@ 5'))"

chr_ord_inverse [rule_format] :
"ALL c. chr(ord'(c)) = makePartial c"

slash_000 [rule_format] : "makePartial '\\000' = chr(0')"

slash_001 [rule_format] : "makePartial '\\001' = chr(1')"

slash_002 [rule_format] : "makePartial '\\002' = chr(2')"

slash_003 [rule_format] : "makePartial '\\003' = chr(3')"

slash_004 [rule_format] : "makePartial '\\004' = chr(4')"

slash_005 [rule_format] : "makePartial '\\005' = chr(5')"

slash_006 [rule_format] : "makePartial '\\006' = chr(6')"

slash_007 [rule_format] : "makePartial '\\007' = chr(7')"

slash_008 [rule_format] : "makePartial '\\008' = chr(8')"

slash_009 [rule_format] : "makePartial '\\009' = chr(9')"

slash_010 [rule_format] : "makePartial '\\010' = chr(1' @@ 0')"

slash_011 [rule_format] : "makePartial '\\011' = chr(1' @@ 1')"

slash_012 [rule_format] : "makePartial '\\012' = chr(1' @@ 2')"

slash_013 [rule_format] : "makePartial '\\013' = chr(1' @@ 3')"

slash_014 [rule_format] : "makePartial '\\014' = chr(1' @@ 4')"

slash_015 [rule_format] : "makePartial '\\015' = chr(1' @@ 5')"

slash_016 [rule_format] : "makePartial '\\016' = chr(1' @@ 6')"

slash_017 [rule_format] : "makePartial '\\017' = chr(1' @@ 7')"

slash_018 [rule_format] : "makePartial '\\018' = chr(1' @@ 8')"

slash_019 [rule_format] : "makePartial '\\019' = chr(1' @@ 9')"

slash_020 [rule_format] : "makePartial '\\020' = chr(2' @@ 0')"

slash_021 [rule_format] : "makePartial '\\021' = chr(2' @@ 1')"

slash_022 [rule_format] : "makePartial '\\022' = chr(2' @@ 2')"

slash_023 [rule_format] : "makePartial '\\023' = chr(2' @@ 3')"

slash_024 [rule_format] : "makePartial '\\024' = chr(2' @@ 4')"

slash_025 [rule_format] : "makePartial '\\025' = chr(2' @@ 5')"

slash_026 [rule_format] : "makePartial '\\026' = chr(2' @@ 6')"

slash_027 [rule_format] : "makePartial '\\027' = chr(2' @@ 7')"

slash_028 [rule_format] : "makePartial '\\028' = chr(2' @@ 8')"

slash_029 [rule_format] : "makePartial '\\029' = chr(2' @@ 9')"

slash_030 [rule_format] : "makePartial '\\030' = chr(3' @@ 0')"

slash_031 [rule_format] : "makePartial '\\031' = chr(3' @@ 1')"

slash_032 [rule_format] : "makePartial '\\032' = chr(3' @@ 2')"

slash_033 [rule_format] : "makePartial '\\033' = chr(3' @@ 3')"

slash_034 [rule_format] : "makePartial '\\034' = chr(3' @@ 4')"

slash_035 [rule_format] : "makePartial '\\035' = chr(3' @@ 5')"

slash_036 [rule_format] : "makePartial '\\036' = chr(3' @@ 6')"

slash_037 [rule_format] : "makePartial '\\037' = chr(3' @@ 7')"

slash_038 [rule_format] : "makePartial '\\038' = chr(3' @@ 8')"

slash_039 [rule_format] : "makePartial '\\039' = chr(3' @@ 9')"

slash_040 [rule_format] : "makePartial '\\040' = chr(4' @@ 0')"

slash_041 [rule_format] : "makePartial '\\041' = chr(4' @@ 1')"

slash_042 [rule_format] : "makePartial '\\042' = chr(4' @@ 2')"

slash_043 [rule_format] : "makePartial '\\043' = chr(4' @@ 3')"

slash_044 [rule_format] : "makePartial '\\044' = chr(4' @@ 4')"

slash_045 [rule_format] : "makePartial '\\045' = chr(4' @@ 5')"

slash_046 [rule_format] : "makePartial '\\046' = chr(4' @@ 6')"

slash_047 [rule_format] : "makePartial '\\047' = chr(4' @@ 7')"

slash_048 [rule_format] : "makePartial '\\048' = chr(4' @@ 8')"

slash_049 [rule_format] : "makePartial '\\049' = chr(4' @@ 9')"

slash_050 [rule_format] : "makePartial '\\050' = chr(5' @@ 0')"

slash_051 [rule_format] : "makePartial '\\051' = chr(5' @@ 1')"

slash_052 [rule_format] : "makePartial '\\052' = chr(5' @@ 2')"

slash_053 [rule_format] : "makePartial '\\053' = chr(5' @@ 3')"

slash_054 [rule_format] : "makePartial '\\054' = chr(5' @@ 4')"

slash_055 [rule_format] : "makePartial '\\055' = chr(5' @@ 5')"

slash_056 [rule_format] : "makePartial '\\056' = chr(5' @@ 6')"

slash_057 [rule_format] : "makePartial '\\057' = chr(5' @@ 7')"

slash_058 [rule_format] : "makePartial '\\058' = chr(5' @@ 8')"

slash_059 [rule_format] : "makePartial '\\059' = chr(5' @@ 9')"

slash_060 [rule_format] : "makePartial '\\060' = chr(6' @@ 0')"

slash_061 [rule_format] : "makePartial '\\061' = chr(6' @@ 1')"

slash_062 [rule_format] : "makePartial '\\062' = chr(6' @@ 2')"

slash_063 [rule_format] : "makePartial '\\063' = chr(6' @@ 3')"

slash_064 [rule_format] : "makePartial '\\064' = chr(6' @@ 4')"

slash_065 [rule_format] : "makePartial '\\065' = chr(6' @@ 5')"

slash_066 [rule_format] : "makePartial '\\066' = chr(6' @@ 6')"

slash_067 [rule_format] : "makePartial '\\067' = chr(6' @@ 7')"

slash_068 [rule_format] : "makePartial '\\068' = chr(6' @@ 8')"

slash_069 [rule_format] : "makePartial '\\069' = chr(6' @@ 9')"

slash_070 [rule_format] : "makePartial '\\070' = chr(7' @@ 0')"

slash_071 [rule_format] : "makePartial '\\071' = chr(7' @@ 1')"

slash_072 [rule_format] : "makePartial '\\072' = chr(7' @@ 2')"

slash_073 [rule_format] : "makePartial '\\073' = chr(7' @@ 3')"

slash_074 [rule_format] : "makePartial '\\074' = chr(7' @@ 4')"

slash_075 [rule_format] : "makePartial '\\075' = chr(7' @@ 5')"

slash_076 [rule_format] : "makePartial '\\076' = chr(7' @@ 6')"

slash_077 [rule_format] : "makePartial '\\077' = chr(7' @@ 7')"

slash_078 [rule_format] : "makePartial '\\078' = chr(7' @@ 8')"

slash_079 [rule_format] : "makePartial '\\079' = chr(7' @@ 9')"

slash_080 [rule_format] : "makePartial '\\080' = chr(8' @@ 0')"

slash_081 [rule_format] : "makePartial '\\081' = chr(8' @@ 1')"

slash_082 [rule_format] : "makePartial '\\082' = chr(8' @@ 2')"

slash_083 [rule_format] : "makePartial '\\083' = chr(8' @@ 3')"

slash_084 [rule_format] : "makePartial '\\084' = chr(8' @@ 4')"

slash_085 [rule_format] : "makePartial '\\085' = chr(8' @@ 5')"

slash_086 [rule_format] : "makePartial '\\086' = chr(8' @@ 6')"

slash_087 [rule_format] : "makePartial '\\087' = chr(8' @@ 7')"

slash_088 [rule_format] : "makePartial '\\088' = chr(8' @@ 8')"

slash_089 [rule_format] : "makePartial '\\089' = chr(8' @@ 9')"

slash_090 [rule_format] : "makePartial '\\090' = chr(9' @@ 0')"

slash_091 [rule_format] : "makePartial '\\091' = chr(9' @@ 1')"

slash_092 [rule_format] : "makePartial '\\092' = chr(9' @@ 2')"

slash_093 [rule_format] : "makePartial '\\093' = chr(9' @@ 3')"

slash_094 [rule_format] : "makePartial '\\094' = chr(9' @@ 4')"

slash_095 [rule_format] : "makePartial '\\095' = chr(9' @@ 5')"

slash_096 [rule_format] : "makePartial '\\096' = chr(9' @@ 6')"

slash_097 [rule_format] : "makePartial '\\097' = chr(9' @@ 7')"

slash_098 [rule_format] : "makePartial '\\098' = chr(9' @@ 8')"

slash_099 [rule_format] : "makePartial '\\099' = chr(9' @@ 9')"

slash_100 [rule_format] :
"makePartial '\\100' = chr(1' @@ (0' @@ 0'))"

slash_101 [rule_format] :
"makePartial '\\101' = chr(1' @@ (0' @@ 1'))"

slash_102 [rule_format] :
"makePartial '\\102' = chr(1' @@ (0' @@ 2'))"

slash_103 [rule_format] :
"makePartial '\\103' = chr(1' @@ (0' @@ 3'))"

slash_104 [rule_format] :
"makePartial '\\104' = chr(1' @@ (0' @@ 4'))"

slash_105 [rule_format] :
"makePartial '\\105' = chr(1' @@ (0' @@ 5'))"

slash_106 [rule_format] :
"makePartial '\\106' = chr(1' @@ (0' @@ 6'))"

slash_107 [rule_format] :
"makePartial '\\107' = chr(1' @@ (0' @@ 7'))"

slash_108 [rule_format] :
"makePartial '\\108' = chr(1' @@ (0' @@ 8'))"

slash_109 [rule_format] :
"makePartial '\\109' = chr(1' @@ (0' @@ 9'))"

slash_110 [rule_format] :
"makePartial '\\110' = chr(1' @@ (1' @@ 0'))"

slash_111 [rule_format] :
"makePartial '\\111' = chr(1' @@ (1' @@ 1'))"

slash_112 [rule_format] :
"makePartial '\\112' = chr(1' @@ (1' @@ 2'))"

slash_113 [rule_format] :
"makePartial '\\113' = chr(1' @@ (1' @@ 3'))"

slash_114 [rule_format] :
"makePartial '\\114' = chr(1' @@ (1' @@ 4'))"

slash_115 [rule_format] :
"makePartial '\\115' = chr(1' @@ (1' @@ 5'))"

slash_116 [rule_format] :
"makePartial '\\116' = chr(1' @@ (1' @@ 6'))"

slash_117 [rule_format] :
"makePartial '\\117' = chr(1' @@ (1' @@ 7'))"

slash_118 [rule_format] :
"makePartial '\\118' = chr(1' @@ (1' @@ 8'))"

slash_119 [rule_format] :
"makePartial '\\119' = chr(1' @@ (1' @@ 9'))"

slash_120 [rule_format] :
"makePartial '\\120' = chr(1' @@ (2' @@ 0'))"

slash_121 [rule_format] :
"makePartial '\\121' = chr(1' @@ (2' @@ 1'))"

slash_122 [rule_format] :
"makePartial '\\122' = chr(1' @@ (2' @@ 2'))"

slash_123 [rule_format] :
"makePartial '\\123' = chr(1' @@ (2' @@ 3'))"

slash_124 [rule_format] :
"makePartial '\\124' = chr(1' @@ (2' @@ 4'))"

slash_125 [rule_format] :
"makePartial '\\125' = chr(1' @@ (2' @@ 5'))"

slash_126 [rule_format] :
"makePartial '\\126' = chr(1' @@ (2' @@ 6'))"

slash_127 [rule_format] :
"makePartial '\\127' = chr(1' @@ (2' @@ 7'))"

slash_128 [rule_format] :
"makePartial '\\128' = chr(1' @@ (2' @@ 8'))"

slash_129 [rule_format] :
"makePartial '\\129' = chr(1' @@ (2' @@ 9'))"

slash_130 [rule_format] :
"makePartial '\\130' = chr(1' @@ (3' @@ 0'))"

slash_131 [rule_format] :
"makePartial '\\131' = chr(1' @@ (3' @@ 1'))"

slash_132 [rule_format] :
"makePartial '\\132' = chr(1' @@ (3' @@ 2'))"

slash_133 [rule_format] :
"makePartial '\\133' = chr(1' @@ (3' @@ 3'))"

slash_134 [rule_format] :
"makePartial '\\134' = chr(1' @@ (3' @@ 4'))"

slash_135 [rule_format] :
"makePartial '\\135' = chr(1' @@ (3' @@ 5'))"

slash_136 [rule_format] :
"makePartial '\\136' = chr(1' @@ (3' @@ 6'))"

slash_137 [rule_format] :
"makePartial '\\137' = chr(1' @@ (3' @@ 7'))"

slash_138 [rule_format] :
"makePartial '\\138' = chr(1' @@ (3' @@ 8'))"

slash_139 [rule_format] :
"makePartial '\\139' = chr(1' @@ (3' @@ 9'))"

slash_140 [rule_format] :
"makePartial '\\140' = chr(1' @@ (4' @@ 0'))"

slash_141 [rule_format] :
"makePartial '\\141' = chr(1' @@ (4' @@ 1'))"

slash_142 [rule_format] :
"makePartial '\\142' = chr(1' @@ (4' @@ 2'))"

slash_143 [rule_format] :
"makePartial '\\143' = chr(1' @@ (4' @@ 3'))"

slash_144 [rule_format] :
"makePartial '\\144' = chr(1' @@ (4' @@ 4'))"

slash_145 [rule_format] :
"makePartial '\\145' = chr(1' @@ (4' @@ 5'))"

slash_146 [rule_format] :
"makePartial '\\146' = chr(1' @@ (4' @@ 6'))"

slash_147 [rule_format] :
"makePartial '\\147' = chr(1' @@ (4' @@ 7'))"

slash_148 [rule_format] :
"makePartial '\\148' = chr(1' @@ (4' @@ 8'))"

slash_149 [rule_format] :
"makePartial '\\149' = chr(1' @@ (4' @@ 9'))"

slash_150 [rule_format] :
"makePartial '\\150' = chr(1' @@ (5' @@ 0'))"

slash_151 [rule_format] :
"makePartial '\\151' = chr(1' @@ (5' @@ 1'))"

slash_152 [rule_format] :
"makePartial '\\152' = chr(1' @@ (5' @@ 2'))"

slash_153 [rule_format] :
"makePartial '\\153' = chr(1' @@ (5' @@ 3'))"

slash_154 [rule_format] :
"makePartial '\\154' = chr(1' @@ (5' @@ 4'))"

slash_155 [rule_format] :
"makePartial '\\155' = chr(1' @@ (5' @@ 5'))"

slash_156 [rule_format] :
"makePartial '\\156' = chr(1' @@ (5' @@ 6'))"

slash_157 [rule_format] :
"makePartial '\\157' = chr(1' @@ (5' @@ 7'))"

slash_158 [rule_format] :
"makePartial '\\158' = chr(1' @@ (5' @@ 8'))"

slash_159 [rule_format] :
"makePartial '\\159' = chr(1' @@ (5' @@ 9'))"

slash_160 [rule_format] :
"makePartial '\\160' = chr(1' @@ (6' @@ 0'))"

slash_161 [rule_format] :
"makePartial '\\161' = chr(1' @@ (6' @@ 1'))"

slash_162 [rule_format] :
"makePartial '\\162' = chr(1' @@ (6' @@ 2'))"

slash_163 [rule_format] :
"makePartial '\\163' = chr(1' @@ (6' @@ 3'))"

slash_164 [rule_format] :
"makePartial '\\164' = chr(1' @@ (6' @@ 4'))"

slash_165 [rule_format] :
"makePartial '\\165' = chr(1' @@ (6' @@ 5'))"

slash_166 [rule_format] :
"makePartial '\\166' = chr(1' @@ (6' @@ 6'))"

slash_167 [rule_format] :
"makePartial '\\167' = chr(1' @@ (6' @@ 7'))"

slash_168 [rule_format] :
"makePartial '\\168' = chr(1' @@ (6' @@ 8'))"

slash_169 [rule_format] :
"makePartial '\\169' = chr(1' @@ (6' @@ 9'))"

slash_170 [rule_format] :
"makePartial '\\170' = chr(1' @@ (7' @@ 0'))"

slash_171 [rule_format] :
"makePartial '\\171' = chr(1' @@ (7' @@ 1'))"

slash_172 [rule_format] :
"makePartial '\\172' = chr(1' @@ (7' @@ 2'))"

slash_173 [rule_format] :
"makePartial '\\173' = chr(1' @@ (7' @@ 3'))"

slash_174 [rule_format] :
"makePartial '\\174' = chr(1' @@ (7' @@ 4'))"

slash_175 [rule_format] :
"makePartial '\\175' = chr(1' @@ (7' @@ 5'))"

slash_176 [rule_format] :
"makePartial '\\176' = chr(1' @@ (7' @@ 6'))"

slash_177 [rule_format] :
"makePartial '\\177' = chr(1' @@ (7' @@ 7'))"

slash_178 [rule_format] :
"makePartial '\\178' = chr(1' @@ (7' @@ 8'))"

slash_179 [rule_format] :
"makePartial '\\179' = chr(1' @@ (7' @@ 9'))"

slash_180 [rule_format] :
"makePartial '\\180' = chr(1' @@ (8' @@ 0'))"

slash_181 [rule_format] :
"makePartial '\\181' = chr(1' @@ (8' @@ 1'))"

slash_182 [rule_format] :
"makePartial '\\182' = chr(1' @@ (8' @@ 2'))"

slash_183 [rule_format] :
"makePartial '\\183' = chr(1' @@ (8' @@ 3'))"

slash_184 [rule_format] :
"makePartial '\\184' = chr(1' @@ (8' @@ 4'))"

slash_185 [rule_format] :
"makePartial '\\185' = chr(1' @@ (8' @@ 5'))"

slash_186 [rule_format] :
"makePartial '\\186' = chr(1' @@ (8' @@ 6'))"

slash_187 [rule_format] :
"makePartial '\\187' = chr(1' @@ (8' @@ 7'))"

slash_188 [rule_format] :
"makePartial '\\188' = chr(1' @@ (8' @@ 8'))"

slash_189 [rule_format] :
"makePartial '\\189' = chr(1' @@ (8' @@ 9'))"

slash_190 [rule_format] :
"makePartial '\\190' = chr(1' @@ (9' @@ 0'))"

slash_191 [rule_format] :
"makePartial '\\191' = chr(1' @@ (9' @@ 1'))"

slash_192 [rule_format] :
"makePartial '\\192' = chr(1' @@ (9' @@ 2'))"

slash_193 [rule_format] :
"makePartial '\\193' = chr(1' @@ (9' @@ 3'))"

slash_194 [rule_format] :
"makePartial '\\194' = chr(1' @@ (9' @@ 4'))"

slash_195 [rule_format] :
"makePartial '\\195' = chr(1' @@ (9' @@ 5'))"

slash_196 [rule_format] :
"makePartial '\\196' = chr(1' @@ (9' @@ 6'))"

slash_197 [rule_format] :
"makePartial '\\197' = chr(1' @@ (9' @@ 7'))"

slash_198 [rule_format] :
"makePartial '\\198' = chr(1' @@ (9' @@ 8'))"

slash_199 [rule_format] :
"makePartial '\\199' = chr(1' @@ (9' @@ 9'))"

slash_200 [rule_format] :
"makePartial '\\200' = chr(2' @@ (0' @@ 0'))"

slash_201 [rule_format] :
"makePartial '\\201' = chr(2' @@ (0' @@ 1'))"

slash_202 [rule_format] :
"makePartial '\\202' = chr(2' @@ (0' @@ 2'))"

slash_203 [rule_format] :
"makePartial '\\203' = chr(2' @@ (0' @@ 3'))"

slash_204 [rule_format] :
"makePartial '\\204' = chr(2' @@ (0' @@ 4'))"

slash_205 [rule_format] :
"makePartial '\\205' = chr(2' @@ (0' @@ 5'))"

slash_206 [rule_format] :
"makePartial '\\206' = chr(2' @@ (0' @@ 6'))"

slash_207 [rule_format] :
"makePartial '\\207' = chr(2' @@ (0' @@ 7'))"

slash_208 [rule_format] :
"makePartial '\\208' = chr(2' @@ (0' @@ 8'))"

slash_209 [rule_format] :
"makePartial '\\209' = chr(2' @@ (0' @@ 9'))"

slash_210 [rule_format] :
"makePartial '\\210' = chr(2' @@ (1' @@ 0'))"

slash_211 [rule_format] :
"makePartial '\\211' = chr(2' @@ (1' @@ 1'))"

slash_212 [rule_format] :
"makePartial '\\212' = chr(2' @@ (1' @@ 2'))"

slash_213 [rule_format] :
"makePartial '\\213' = chr(2' @@ (1' @@ 3'))"

slash_214 [rule_format] :
"makePartial '\\214' = chr(2' @@ (1' @@ 4'))"

slash_215 [rule_format] :
"makePartial '\\215' = chr(2' @@ (1' @@ 5'))"

slash_216 [rule_format] :
"makePartial '\\216' = chr(2' @@ (1' @@ 6'))"

slash_217 [rule_format] :
"makePartial '\\217' = chr(2' @@ (1' @@ 7'))"

slash_218 [rule_format] :
"makePartial '\\218' = chr(2' @@ (1' @@ 8'))"

slash_219 [rule_format] :
"makePartial '\\219' = chr(2' @@ (1' @@ 9'))"

slash_220 [rule_format] :
"makePartial '\\220' = chr(2' @@ (2' @@ 0'))"

slash_221 [rule_format] :
"makePartial '\\221' = chr(2' @@ (2' @@ 1'))"

slash_222 [rule_format] :
"makePartial '\\222' = chr(2' @@ (2' @@ 2'))"

slash_223 [rule_format] :
"makePartial '\\223' = chr(2' @@ (2' @@ 3'))"

slash_224 [rule_format] :
"makePartial '\\224' = chr(2' @@ (2' @@ 4'))"

slash_225 [rule_format] :
"makePartial '\\225' = chr(2' @@ (2' @@ 5'))"

slash_226 [rule_format] :
"makePartial '\\226' = chr(2' @@ (2' @@ 6'))"

slash_227 [rule_format] :
"makePartial '\\227' = chr(2' @@ (2' @@ 7'))"

slash_228 [rule_format] :
"makePartial '\\228' = chr(2' @@ (2' @@ 8'))"

slash_229 [rule_format] :
"makePartial '\\229' = chr(2' @@ (2' @@ 9'))"

slash_230 [rule_format] :
"makePartial '\\230' = chr(2' @@ (3' @@ 0'))"

slash_231 [rule_format] :
"makePartial '\\231' = chr(2' @@ (3' @@ 1'))"

slash_232 [rule_format] :
"makePartial '\\232' = chr(2' @@ (3' @@ 2'))"

slash_233 [rule_format] :
"makePartial '\\233' = chr(2' @@ (3' @@ 3'))"

slash_234 [rule_format] :
"makePartial '\\234' = chr(2' @@ (3' @@ 4'))"

slash_235 [rule_format] :
"makePartial '\\235' = chr(2' @@ (3' @@ 5'))"

slash_236 [rule_format] :
"makePartial '\\236' = chr(2' @@ (3' @@ 6'))"

slash_237 [rule_format] :
"makePartial '\\237' = chr(2' @@ (3' @@ 7'))"

slash_238 [rule_format] :
"makePartial '\\238' = chr(2' @@ (3' @@ 8'))"

slash_239 [rule_format] :
"makePartial '\\239' = chr(2' @@ (3' @@ 9'))"

slash_240 [rule_format] :
"makePartial '\\240' = chr(2' @@ (4' @@ 0'))"

slash_241 [rule_format] :
"makePartial '\\241' = chr(2' @@ (4' @@ 1'))"

slash_242 [rule_format] :
"makePartial '\\242' = chr(2' @@ (4' @@ 2'))"

slash_243 [rule_format] :
"makePartial '\\243' = chr(2' @@ (4' @@ 3'))"

slash_244 [rule_format] :
"makePartial '\\244' = chr(2' @@ (4' @@ 4'))"

slash_245 [rule_format] :
"makePartial '\\245' = chr(2' @@ (4' @@ 5'))"

slash_246 [rule_format] :
"makePartial '\\246' = chr(2' @@ (4' @@ 6'))"

slash_247 [rule_format] :
"makePartial '\\247' = chr(2' @@ (4' @@ 7'))"

slash_248 [rule_format] :
"makePartial '\\248' = chr(2' @@ (4' @@ 8'))"

slash_249 [rule_format] :
"makePartial '\\249' = chr(2' @@ (4' @@ 9'))"

slash_250 [rule_format] :
"makePartial '\\250' = chr(2' @@ (5' @@ 0'))"

slash_251 [rule_format] :
"makePartial '\\251' = chr(2' @@ (5' @@ 1'))"

slash_252 [rule_format] :
"makePartial '\\252' = chr(2' @@ (5' @@ 2'))"

slash_253 [rule_format] :
"makePartial '\\253' = chr(2' @@ (5' @@ 3'))"

slash_254 [rule_format] :
"makePartial '\\254' = chr(2' @@ (5' @@ 4'))"

slash_255 [rule_format] :
"makePartial '\\255' = chr(2' @@ (5' @@ 5'))"

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

isLetter_def [rule_format] :
"ALL c.
 isLetter(c) =
 (ord'('A') <=' ord'(c) & ord'(c) <=' ord'('Z') |
  ord'('a') <=' ord'(c) & ord'(c) <=' ord'('z'))"

isDigit_def [rule_format] :
"ALL c.
 isDigit(c) = (ord'('0') <=' ord'(c) & ord'(c) <=' ord'('9'))"

isPrintable_def [rule_format] :
"ALL c.
 isPrintable(c) = (ord'(' ') <=' ord'(c) & ord'(c) <=' ord'('~'))"

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

ICE01 [rule_format] : "ALL x. ALL y. ord'(x) ==' ord'(y) = x ==' y"

ICE02 [rule_format] :
"ALL x. ALL y. Not' (ord'(x) ==' ord'(y)) = x /= y"

ICO01 [rule_format] :
"ALL x. ALL y. compare x y ==' EQ = ord'(x) ==' ord'(y)"

ICO02 [rule_format] :
"ALL x. ALL y. compare x y ==' LT = ord'(x) <'' ord'(y)"

ICO03 [rule_format] :
"ALL x. ALL y. compare x y ==' GT = ord'(x) >'' ord'(y)"

ICO04 [rule_format] : "ALL x. ALL y. ord'(x) <'' ord'(y) = x <'' y"

ICO08 [rule_format] :
"ALL x. ALL y. ord'(x) <='' ord'(y) = X_maxX2 x y ==' y"

ICO10 [rule_format] :
"ALL x. ALL y. ord'(x) <='' ord'(y) = X_minX2 x y ==' x"

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
declare leq_def2_Nat [simp]
declare leq_def3_Nat [simp]
declare even_0_Nat [simp]
declare even_suc_Nat [simp]
declare factorial_0 [simp]
declare add_0_Nat [simp]
declare mult_0_Nat [simp]
declare power_0_Nat [simp]
declare subTotal_def1_Nat [simp]
declare subTotal_def2_Nat [simp]
declare sub_dom_Nat [simp]
declare divide_0_Nat [simp]
declare min_0 [simp]
declare NotFalse [simp]
declare NotTrue [simp]
declare AndFalse [simp]
declare AndTrue [simp]
declare EqualReflex [simp]
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
declare IUO05 [simp]
declare IUO06 [simp]
declare IUO07 [simp]
declare chr_ord_inverse [simp]
declare ICE01 [simp]
declare ICE02 [simp]
declare ICO04 [simp]

theorem ICO05 : "ALL x. ALL y. ord'(x) <='' ord'(y) = x <='' y"
apply(rule allI)+
apply(simp add: LeqDef)
done 

ML "Header.record \"ICO05\""

theorem ICO06 : "ALL x. ALL y. ord'(x) >'' ord'(y) = x >'' y"
apply(rule allI)+
apply(simp add: GeDef)
done 

ML "Header.record \"ICO06\""

theorem ICO07 : "ALL x. ALL y. ord'(x) >='' ord'(y) = x >='' y"
apply(rule allI)+
apply(simp only: GeqDef)
apply(simp add: GeDef)
done 

ML "Header.record \"ICO07\""

theorem ICO09 :
"ALL x. ALL y. ord'(y) <='' ord'(x) = X_maxX2 x y ==' x"
apply(rule allI)+
apply(simp add: LeqDef)
done 


ML "Header.record \"ICO09\""

theorem ICO11 :
"ALL x. ALL y. ord'(y) <='' ord'(x) = X_minX2 x y ==' y"
apply(rule allI)+
apply(simp add: LeqDef)
done 

ML "Header.record \"ICO11\""

end
