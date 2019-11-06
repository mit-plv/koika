class extfuns {
public:
  bits<3> f0(const bits<3> arg) {
    return prims::lnot<3>(arg);
  }
};
