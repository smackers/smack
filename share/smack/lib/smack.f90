!
! This file is distributed under the MIT License. See LICENSE for details.
!

module smack
  implicit none
      interface
        subroutine __verifier_assert(cond) bind(c, name="__VERIFIER_assert")
          use, intrinsic :: iso_c_binding, only: c_int
          implicit none
          integer(c_int), value :: cond
        end subroutine __verifier_assert
      end interface
  contains
    subroutine assert(cond) 
      use, intrinsic :: iso_c_binding, only: c_int
      implicit none
      logical, intent(in) :: cond
      integer(c_int), value :: cond_c
      interface
        subroutine __verifier_assert(cond) bind(c, name="__VERIFIER_assert")
          use, intrinsic :: iso_c_binding, only: c_int
          implicit none
          integer(c_int), value :: cond
        end subroutine __verifier_assert
      end interface
      cond_c = merge(1,0,cond)
      call __verifier_assert(cond_c)
    end subroutine assert
end
