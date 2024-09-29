test tcSingleThread [main=TestWithSingleThread]:
  assert FinalValueIsCorrect in
  (union Thread, {TestWithSingleThread});

test tcManyThreads [main=TestWithManyThreads]:
  assert FinalValueIsCorrect in
  (union Thread, {TestWithManyThreads});