method CylinderVolume(radius :real, height: real)
  returns (volume: real)
  requires radius >= 0.0 && height >= 0.0
  ensures volume >= 0.0
{
  volume := 3.14 * radius * radius * height;
}

method main(){
  var a := CylinderVolume(3.0,4.0);
}