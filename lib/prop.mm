$c wff $.
$c |- $.
$c -> $.
$c ( $.
$c ) $.
$v ph $.
wph $f wff ph $.
$v ps $.
wps $f wff ps $.
$v ch $.
wch $f wff ch $.
$v th $.
wth $f wff th $.
$v ta $.
wta $f wff ta $.
${
  wi $a wff ( ph -> ps ) $.
$}
${
  min $e |- ph $.
  maj $e |- ( ph -> ps ) $.
  mp $a |- ps $.
$}
${
  simp $a |- ( ph -> ( ps -> ph ) ) $.
$}
${
  frege $a |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) $.
$}
${
  mp2.1 $e |- ph $.
  mp2.2 $e |- ps $.
  mp2.3 $e |- ( ph -> ( ps -> ch ) ) $.
  mp2 $p |- ch $= wps wch mp2.2 wph wps wch wi mp2.1 mp2.3 mp mp $.
$}
