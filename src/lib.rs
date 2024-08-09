use rug::{Assign, Integer};
//use smallvec::{SmallVec};

pub fn factorial(n: usize) -> usize {
    let mut result = 1;
    for i in 2..=n {
        result *= i;
    }
    result
}

pub fn choose(n: usize, k: usize) -> usize {
    let mut k = k;
    if k > n-k {
        k = n-k;
    }

    let mut result = 1;
    for i in 0..k {
        result *= n-i;
        result /= i+1;
    }
    result
}

pub fn usize_to_vec_of_set_bits(v: usize) -> Vec<usize> {
  let mut w: usize = v;
  let mut ret_vec = Vec::<usize>::new();
  
  while w > 0 {
    let index: usize = w.trailing_zeros() as usize;
    ret_vec.push(index);
    w ^= 1 << index;
  }
  return ret_vec;
}

pub fn get_next_bit_permutation(v: usize) -> usize {
    let t: usize = v | (v-1);
    (t + 1) | (((!t & (!t).wrapping_neg()) - 1) >> (v.trailing_zeros() + 1))
}

pub fn set_next_bit_permutation(v: &mut usize) {
    let t: usize = *v | (*v-1);
    *v = (t + 1) | (((!t & (!t).wrapping_neg()) - 1) >> (v.trailing_zeros() + 1))
}

pub fn set_next_bit_permutation_u16(v: &mut u16) {
    let t: u16 = *v | (*v-1);
    *v = (t + 1) | (((!t & (!t).wrapping_neg()) - 1) >> (v.trailing_zeros() + 1))
}

pub fn set_next_bit_permutation_u32(v: &mut u32) {
    let t: u32 = *v | (*v-1);
    *v = (t + 1) | (((!t & (!t).wrapping_neg()) - 1) >> (v.trailing_zeros() + 1))
}

pub fn set_next_bit_permutation_u64(v: &mut u64) {
    let t: u64 = *v | (*v-1);
    *v = (t + 1) | (((!t & (!t).wrapping_neg()) - 1) >> (v.trailing_zeros() + 1))
}


pub struct SetBitGetter {
  val: u64,
  bit: u64,
}

impl SetBitGetter {
  pub fn new() -> Self {
    SetBitGetter {
      val: 0,
      bit: 0
    }
  }
  
  pub fn reset(&mut self, val: u64) {
    self.val = val;
  }
  
  pub fn are_there_more_bits(&self) -> bool {
    return self.val > 0;
  }
  
  pub fn get_bit(&mut self) -> u64 {
    self.bit = 1 << self.val.trailing_zeros();
    self.val ^= self.bit;
    return self.bit;
  }
}

/*
pub struct Subsets {
  indices: SmallVec::<[usize; 20]>,
  set_size: usize,
  subset_size: usize,
  done: bool,
  next_counter_threshold: usize,
  next_counter: usize,
}

impl Subsets {
  pub fn new() -> Self {
    let mut indices = SmallVec::with_capacity(20);
    for _i in 0..19 {
      indices.push(0);
    }
    
    let s = Subsets {
      indices,
      set_size: 0,
      subset_size: 0,
      done: false,
      next_counter_threshold: 0,
      next_counter: 0,
    };
    return s
  }
  
  pub fn reset(&mut self, set_size: usize, subset_size: usize) {
    self.set_size = set_size;
    self.subset_size = subset_size;
    
    self.indices[subset_size] = 100; // a convenience for the next() method
    
    for i in 0..subset_size {
      self.indices[i] = i;
    }
    
    self.done = false;
    self.next_counter_threshold = choose(set_size, subset_size) - 1;
    self.next_counter = 0;
  }
  

  pub fn next_new(&mut self) {
    self.next_counter += 1;
    for i in 0..self.subset_size {
      unsafe {
        if *self.indices.get_unchecked(i+1) > *self.indices.get_unchecked(i) + 1 {
          *self.indices.get_unchecked_mut(i) += 1;
          if self.next_counter == self.next_counter_threshold {
            self.done = true;
          } 
          break;
        } else {
          *self.indices.get_unchecked_mut(i) = i;
        }
      }
    }
  }
  

  pub fn next(&mut self) {
    for i in 0..self.subset_size {
      unsafe {
        if *self.indices.get_unchecked(i+1) > *self.indices.get_unchecked(i) + 1 {
          *self.indices.get_unchecked_mut(i) += 1;
          if i == self.subset_size - 1 && *self.indices.get_unchecked_mut(i) == self.set_size {
            self.done = true;
          } 
          break;
        } else {
          *self.indices.get_unchecked_mut(i) = i;
        }
      }
    }
  }
  
  pub fn is_done(&self) -> bool {
    return self.done;
  }
  
  pub fn get_indices_ref(&self) -> &SmallVec::<[usize; 20]> {
    &self.indices
  }
}
*/

pub struct Combinations {
    result: Integer,
    temp1: Integer,
    temp2: Integer,
    temp3: Integer,
}

impl Combinations {
    pub fn new(upper_bound_length: usize, set_bit_count: u32) -> Self {
        let mut result = Integer::with_capacity(upper_bound_length);
        for i in 0..set_bit_count {
            result.set_bit(i, true);
        }

        // Create a temporary `Combinations` object to initialize `temp1` with `result`
        let mut comb = Self {
            result,
            temp1: Integer::with_capacity(upper_bound_length),
            temp2: Integer::with_capacity(upper_bound_length),
            temp3: Integer::with_capacity(upper_bound_length),
        };

        comb.temp1.assign(&comb.result);
        
        comb
    }
    
    pub fn get_next_index(&mut self) -> usize {
      //println!("        pre tmp1: {0:b}", self.temp1);
      let index: u32 = trailing_zeros_builtin(&mut self.temp1);
      self.temp1.set_bit(index, false);
      //println!("        pst tmp1: {0:b}\n", self.temp1);
      return index as usize;
    }
    
    pub fn print_result(&self) {
      println!("{0:b}", &self.result)
    }
}

/*
/// This is an operation `rug` doesn't natively provide. It can be accelerated more if it's a hotspot,
/// via SIMD and such.
fn trailing_zeros_custom(v: &Integer) -> u32 {
    let mut result = 0;
    for &limb in v.as_limbs().iter().rev() {
        let trailing_zeros = limb.trailing_zeros();
        result += trailing_zeros;
        if trailing_zeros < gmp_mpfr_sys::gmp::limb_t::BITS {
            break;
        }
    }
    result
}
*/

fn trailing_zeros_builtin(v: &Integer) -> u32 {
  v.find_one(0).unwrap()
}

pub fn set_next_bit_permutation_v2(v: &mut Combinations) {
    v.temp1.assign(&v.result - 1);
    v.temp1 |= &v.result;
    v.temp2.assign(!&v.temp1);
    v.temp1 += 1;
    v.temp3.assign(-&v.temp2);
    v.temp2 &= &v.temp3;
    v.temp2 -= 1;
    v.temp2 >>= trailing_zeros_builtin(&v.result) + 1;
    v.result.assign(&v.temp1 | &v.temp2);
    v.temp1.assign(&v.result);
}


#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_factorial() {
    let result = factorial(5);
    assert_eq!(result, 120);
  }

  #[test]
  fn test_choose() {
    let result = choose(9, 3);
    assert_eq!(result, 84);
  }

  #[test]
  fn test_get_next_bit_permutation() {
    let result = get_next_bit_permutation(0b0101000usize);
    assert_eq!(result, 0b0110000usize);
  }

  #[test]
  fn test_set_next_bit_permutation() {
    let mut v = 0b0101000usize;
    set_next_bit_permutation(&mut v);
    assert_eq!(v, 0b0110000usize);
  }

  #[test]
  fn test_set_next_bit_permutation_v2() {
    let mut combinations = Combinations::new(7, (3) as u32);
    assert_eq!(combinations.result, Integer::from(7));
    
    set_next_bit_permutation_v2(&mut combinations);
    assert_eq!(combinations.result, Integer::from(11));
    
    set_next_bit_permutation_v2(&mut combinations);
    assert_eq!(combinations.result, Integer::from(13));
    
    set_next_bit_permutation_v2(&mut combinations);
    assert_eq!(combinations.result, Integer::from(14));
    
    set_next_bit_permutation_v2(&mut combinations);
    assert_eq!(combinations.result, Integer::from(19));
    
    set_next_bit_permutation_v2(&mut combinations);
    assert_eq!(combinations.result, Integer::from(21));
  }
  
/*  #[test]
  fn test_subsets() {
    let mut subsets = Subsets::new();
    subsets.reset(5, 3);
    // [0, 1, 2]
    assert_eq!(subsets.get_indices_ref()[2], 2);
    
    subsets.next();
    // [0, 1, 3]
    assert_eq!(subsets.get_indices_ref()[2], 3);
    
    subsets.next();
    // [0, 2, 3]
    assert_eq!(subsets.get_indices_ref()[1], 2);
    assert_eq!(subsets.is_done(), false);
    
    subsets.reset(3, 2); // [0, 1]
    subsets.next();      // [0, 2]
    subsets.next();      // [1, 2]
    assert_eq!(subsets.get_indices_ref()[0], 1);
    assert_eq!(subsets.is_done(), true);
  }*/
  
/*
  #[test]
  fn test_trailing_zeros_custom() {
    assert_eq!(trailing_zeros_custom(&Integer::from(16)), 4);
  }
*/

  #[test]
  fn test_trailing_zeros_builtin() {
    assert_eq!(trailing_zeros_builtin(&Integer::from(16)), 4);
  } 
  
  #[test]
  fn test_get_set_bits() {
    let mut gsb = SetBitGetter::new();
    gsb.reset(13); //  1101 
    assert_eq!(gsb.get_bit(), 1);
    assert_eq!(gsb.get_bit(), 4);
    assert_eq!(gsb.are_there_more_bits(), true);
    assert_eq!(gsb.get_bit(), 8);
    assert_eq!(gsb.are_there_more_bits(), false);
  } 
}
