/*! C++ implementation of external functions for the fir example !*/

#ifndef _EXTFUNS_HPP
#define _EXTFUNS_HPP
class extfuns {
public:
  bits<8> mod19(const bits<8> idx) {
    return bits<8>::mk(idx.v % 19);
  }
};
#endif
