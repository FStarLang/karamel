/* krml header omitted for test repeatability */


#include "CommentFusion.h"

int32_t CommentFusion_test_adjacent_comments(int32_t x)
{
  //
  // First comment
  // Second comment
  // Third comment
  //

  return x;
}

int32_t CommentFusion_test_separated_comments(int32_t x)
{
  //
  // Comment before call
  //

  CommentFusion_side_effect(x);

  //
  // Comment after call
  //

  return x;
}

int32_t CommentFusion_test_mixed_comments(int32_t x)
{
  //
  // Block 1 line 1
  // Block 1 line 2
  //

  CommentFusion_side_effect(x);

  //
  // Block 2 line 1
  // Block 2 line 2
  // Block 2 line 3
  //

  return x;
}

int32_t CommentFusion_test_single_comment(int32_t x)
{
  //
  // Just one comment
  //

  return x;
}

