lib.vo lib.glob lib.v.beautified: lib.v
lib.vio: lib.v
vmtype.vo vmtype.glob vmtype.v.beautified: vmtype.v lib.vo
vmtype.vio: vmtype.v lib.vio
heritage.vo heritage.glob heritage.v.beautified: heritage.v vmtype.vo
heritage.vio: heritage.v vmtype.vio
TacNewHyps.vo TacNewHyps.glob TacNewHyps.v.beautified: TacNewHyps.v
TacNewHyps.vio: TacNewHyps.v
LibHypsNaming.vo LibHypsNaming.glob LibHypsNaming.v.beautified: LibHypsNaming.v TacNewHyps.vo
LibHypsNaming.vio: LibHypsNaming.v TacNewHyps.vio
vmdefinition.vo vmdefinition.glob vmdefinition.v.beautified: vmdefinition.v heritage.vo vmtype.vo LibHypsNaming.vo TacNewHyps.vo
vmdefinition.vio: vmdefinition.v heritage.vio vmtype.vio LibHypsNaming.vio TacNewHyps.vio
ovm.vo ovm.glob ovm.v.beautified: ovm.v LibHypsNaming.vo heritage.vo vmtype.vo vmdefinition.vo
ovm.vio: ovm.v LibHypsNaming.vio heritage.vio vmtype.vio vmdefinition.vio
dvm.vo dvm.glob dvm.v.beautified: dvm.v LibHypsNaming.vo heritage.vo vmtype.vo vmdefinition.vo
dvm.vio: dvm.v LibHypsNaming.vio heritage.vio vmtype.vio vmdefinition.vio
offensive_correct.vo offensive_correct.glob offensive_correct.v.beautified: offensive_correct.v vmtype.vo heritage.vo dvm.vo ovm.vo
offensive_correct.vio: offensive_correct.v vmtype.vio heritage.vio dvm.vio ovm.vio
avm.vo avm.glob avm.v.beautified: avm.v heritage.vo vmtype.vo vmdefinition.vo LibHypsNaming.vo
avm.vio: avm.v heritage.vio vmtype.vio vmdefinition.vio LibHypsNaming.vio
abstract_correct.vo abstract_correct.glob abstract_correct.v.beautified: abstract_correct.v LibHypsNaming.vo lib.vo heritage.vo lib.vo vmtype.vo dvm.vo avm.vo
abstract_correct.vio: abstract_correct.v LibHypsNaming.vio lib.vio heritage.vio lib.vio vmtype.vio dvm.vio avm.vio
