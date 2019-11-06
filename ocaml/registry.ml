let registered_interop_packages : Cuttlebone.Extr.interop_package_t list ref =
  ref []

let register (ip: Cuttlebone.Extr.interop_package_t) =
  registered_interop_packages := ip :: !registered_interop_packages

let reset () =
  let packages = !registered_interop_packages in
  registered_interop_packages := [];
  packages
